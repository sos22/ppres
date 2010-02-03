/* Interpreter for Valgrind intermediate code which tracks some bits
   of metadata e.g. where a particular value actually came from. */
#include <stddef.h>
#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcsignal.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_signals.h"
#include "pub_tool_tooliface.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "libvex_ir.h"
#include "libvex.h"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"
#include "../VEX/priv/ir_opt.h"
#include "../coregrind/pub_core_basics.h"
#include "../coregrind/pub_core_machine.h"
#include "../coregrind/pub_core_dispatch_asm.h"
#include "../coregrind/pub_core_threadstate.h"

#include "replay2.h"

extern void VG_(init_vex)(void);
extern void vexSetAllocModeTEMP_and_clear ( void );

static void eval_expression(struct interpret_state *state,
			    struct expression_result *dest,
			    IRExpr *expr);

static void
init_register(struct abstract_interpret_value *aiv,
	      unsigned name,
	      unsigned long value)
{
	aiv->v = value;
	aiv->origin = expr_reg(name, value);
}

static void
initialise_is_for_vex_state(struct interpret_state *is,
			    const VexGuestAMD64State *state)
{
	unsigned x;
	for (x = 0; x <= REG_LAST; x++)
		init_register(&is->registers[x], x, (&state->guest_RAX)[x]);
}

void
initialise_interpreter_state(void)
{
	struct replay_thread *rt;
	ThreadState *ts;

	tl_assert(head_interpret_mem_lookaside == NULL);
	for (rt = head_thread; rt; rt = rt->next) {
		if (rt->dead)
			continue;
		ts = VG_(get_ThreadState)(rt->id);
		initialise_is_for_vex_state(&rt->interpret_state,
					    &ts->arch.vex);
	}
}

static unsigned long
commit_register(struct abstract_interpret_value *aiv)
{
	aiv->origin = NULL;
	return aiv->v;
}

static void
commit_is_to_vex_state(struct interpret_state *is,
		       VexGuestArchState *state)
{
	unsigned x;
	for (x = 0; x <= REG_LAST; x++)
		(&state->guest_RAX)[x] = commit_register(&is->registers[x]);
}

void
commit_interpreter_state(void)
{
	struct replay_thread *rt;
	ThreadState *ts;
	struct interpret_mem_lookaside *iml, *next;

	for (rt = head_thread; rt; rt = rt->next) {
		if (rt->dead)
			continue;
		ts = VG_(get_ThreadState)(rt->id);
		commit_is_to_vex_state(&rt->interpret_state,
				       &ts->arch.vex);
	}
	/* Actual memory is already correct, so this just needs to
	   release all the slots. */
	for (iml = head_interpret_mem_lookaside;
	     iml != NULL;
	     iml = next) {
		next = iml->next;
		VG_(free)(iml);
	}
	head_interpret_mem_lookaside = NULL;
}

static Bool
chase_into_ok(void *ignore, Addr64 ignore2)
{
	return True;
}

/* Interpret the client, detecting control flow dependencies as we
   go. */
static struct abstract_interpret_value *
get_aiv_for_offset(struct interpret_state *state, Int offset)
{
	tl_assert(!(offset % 8));
	tl_assert(offset / 8 <= REG_LAST);
	return &state->registers[offset / 8];
}

static const struct expression *
read_reg(struct interpret_state *state, unsigned offset, unsigned long *v)
{
	struct abstract_interpret_value *aiv = get_aiv_for_offset(state, offset);
	*v = aiv->v;
	return aiv->origin;
}

static void
interpret_create_mem_lookaside(unsigned long ptr,
			       unsigned size,
			       struct abstract_interpret_value data)
{
	struct interpret_mem_lookaside *iml;
	iml = VG_(malloc)("iml", sizeof(*iml));
	iml->ptr = ptr;
	iml->aiv = data;
	iml->size = size;
	iml->next = head_interpret_mem_lookaside;
	head_interpret_mem_lookaside = iml;

	VG_(memcpy)((void *)ptr, &data.v, size);
}

static const struct expression *
find_origin_expression(struct interpret_mem_lookaside *iml,
		       unsigned size,
		       unsigned long addr)
{
	unsigned long t;
	while (iml) {
		if (iml->ptr == addr && iml->size == size)
			return iml->aiv.origin;
		if (iml->ptr <= addr && iml->ptr + iml->size >= addr + size) {
			unsigned long mask;
			switch (size) {
			case 1: mask = 0xff; break;
			case 2: mask = 0xffff; break;
			case 4: mask = 0xffffffff; break;
			default: ASSUME(0);
			}
			return expr_and(expr_shrl(iml->aiv.origin,
						  expr_const((addr - iml->ptr) * 8)),
					expr_const(mask));
		}
		if (iml->ptr < addr + size &&
		    iml->ptr + iml->size > addr) {
			return expr_combine(iml->aiv.origin,
					    find_origin_expression(iml->next, size, addr));
		}
		iml = iml->next;
	}
	VG_(memcpy)(&t, (void *)addr, size);
	return expr_imported(t);
}

static void
interpreter_do_load(struct expression_result *er,
		    unsigned size,
		    struct abstract_interpret_value addr)
{
	VG_(memset)(er, 0, sizeof(*er));
	if (size > 8) {
		tl_assert(size == 16);
		er->hi.origin =
			expr_mem(8,
				 expr_add(addr.origin, expr_const(8)),
				 find_origin_expression(head_interpret_mem_lookaside,
							8,
							addr.v + 8));
		VG_(memcpy)(&er->hi.v, (const void *)addr.v + 8, 8);
		size = 8;
	} else {
		er->hi.origin = NULL;
	}
	VG_(memcpy)(&er->lo.v, (const void *)addr.v, size);
	er->lo.origin =
		expr_mem(size,
			 addr.origin,
			 find_origin_expression(head_interpret_mem_lookaside,
						size,
						addr.v));
}

static void
do_ccall_calculate_condition(struct interpret_state *state,
			     struct expression_result *dest,
			     IRCallee *cee,
			     IRType retty,
			     IRExpr **args)
{
	struct expression_result condcode = {};
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};
	int inv;

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(state, &condcode, args[0]);
	eval_expression(state, &op, args[1]);

	eval_expression(state, &dep1, args[2]);
	eval_expression(state, &dep2, args[3]);
	eval_expression(state, &ndep, args[4]);
	inv = condcode.lo.v & 1;
	switch (condcode.lo.v & ~1) {
	case AMD64CondZ:
		switch (op.lo.v) {
		case AMD64G_CC_OP_LOGICB:
		case AMD64G_CC_OP_LOGICW:
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = dep1.lo.v == 0;
			dest->lo.origin = expr_eq(dep1.lo.origin,
						  expr_const(0));
			break;
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v == dep2.lo.v;
			dest->lo.origin = expr_eq(dep1.lo.origin,
						  dep2.lo.origin);
			break;

		case AMD64G_CC_OP_ADDL:
			dest->lo.v = (unsigned)(dep1.lo.v + dep2.lo.v) == 0;
			dest->lo.origin = expr_eq(expr_and(expr_add(dep1.lo.origin,
								    dep2.lo.origin),
							   expr_const(0xffffffff)),
						  expr_const(0));
			break;

		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = dep1.lo.v + dep2.lo.v == 0;
			dest->lo.origin = expr_eq(expr_add(dep1.lo.origin,
							   dep2.lo.origin),
						  expr_const(0));
			break;

		case AMD64G_CC_OP_INCB:
		case AMD64G_CC_OP_INCW:
		case AMD64G_CC_OP_INCL:
		case AMD64G_CC_OP_INCQ:
		case AMD64G_CC_OP_DECB:
		case AMD64G_CC_OP_DECW:
		case AMD64G_CC_OP_DECL:
		case AMD64G_CC_OP_DECQ:
		case AMD64G_CC_OP_SHRL:
		case AMD64G_CC_OP_SHRQ:
			dest->lo.v = dep1.lo.v == 0;
			dest->lo.origin = expr_eq(dep1.lo.origin, expr_const(0));
			break;
		default:
			VG_(printf)("Strange operation code %ld\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	case AMD64CondL:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (int)dep1.lo.v < (int)dep2.lo.v;
			dest->lo.origin =
				expr_b(expr_and(expr_add(dep1.lo.origin,
							 expr_const(0x80000000)),
						 expr_const(0xffffffff)),
					expr_and(expr_add(dep2.lo.origin,
							  expr_const(0x80000000)),
						 expr_const(0xffffffff)));
			break;
		default:
			VG_(printf)("Strange operation code %ld for lt\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	case AMD64CondLE:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
			dest->lo.v = (signed char)dep1.lo.v <= (signed char)dep2.lo.v;
			dest->lo.origin =
				expr_be(expr_and(expr_add(dep1.lo.origin,
							  expr_const(0x80)),
						 expr_const(0xff)),
					expr_and(expr_add(dep2.lo.origin,
							  expr_const(0x80)),
						 expr_const(0xff)));
			break;
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (int)dep1.lo.v <= (int)dep2.lo.v;
			dest->lo.origin =
				expr_be(expr_and(expr_add(dep1.lo.origin,
							  expr_const(0x80000000)),
						 expr_const(0xffffffff)),
					expr_and(expr_add(dep2.lo.origin,
							  expr_const(0x80000000)),
						 expr_const(0xffffffff)));
			break;
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = (long)dep1.lo.v <= (long)dep2.lo.v;
			dest->lo.origin = expr_le(dep1.lo.origin, dep2.lo.origin);
			break;
		case AMD64G_CC_OP_LOGICL:
			dest->lo.v = (unsigned)(dep1.lo.v + 0x80000000) <= 0x80000000 ;
			dest->lo.origin = expr_le(expr_and(expr_add(dep1.lo.origin,
								    expr_const(0x80000000)),
							   expr_const(0xffffffff)),
						  expr_const(0x80000000));
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = (long)dep1.lo.v <= 0;
			dest->lo.origin = expr_le(dep1.lo.origin,
						  expr_const(0));
			break;
		default:
			VG_(printf)("Strange operation code %ld for le\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;
	case AMD64CondB:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v < dep2.lo.v;
			dest->lo.origin = expr_b(dep1.lo.origin, dep2.lo.origin);
			break;
		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = dep1.lo.v + dep2.lo.v < dep1.lo.v;
			dest->lo.origin = expr_b(expr_add(dep1.lo.origin,
						       dep2.lo.origin),
					      dep1.lo.origin);
			break;
		default:
			VG_(printf)("Strange operation code %ld for b\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;
	case AMD64CondBE:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v <= dep2.lo.v;
			dest->lo.origin = expr_be(dep1.lo.origin,
					       dep2.lo.origin);
			break;
		default:
			VG_(printf)("Strange operation code %ld for be\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	case AMD64CondS:
		switch (op.lo.v) {
		case AMD64G_CC_OP_LOGICB:
			dest->lo.v = dep1.lo.v >> 7;
			dest->lo.origin = expr_shrl(dep1.lo.origin,
						    expr_const(7));
			break;
		case AMD64G_CC_OP_LOGICW:
			dest->lo.v = dep1.lo.v >> 15;
			dest->lo.origin = expr_shrl(dep1.lo.origin,
						    expr_const(15));
			break;
		case AMD64G_CC_OP_LOGICL:
			dest->lo.v = dep1.lo.v >> 31;
			dest->lo.origin = expr_shrl(dep1.lo.origin,
						 expr_const(31));
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = dep1.lo.v >> 63;
			dest->lo.origin = expr_shrl(dep1.lo.origin,
						 expr_const(63));
			break;
		case AMD64G_CC_OP_SUBB:
			dest->lo.v = (char)dep1.lo.v < (char)dep2.lo.v;
			dest->lo.origin =
				expr_b(expr_and(expr_add(dep1.lo.origin,
							 expr_const(0x80)),
						expr_const(0xff)),
				       expr_and(expr_add(dep2.lo.origin,
							 expr_const(0x80)),
						expr_const(0xff)));
			break;
		case AMD64G_CC_OP_SUBW:
			dest->lo.v = (short)dep1.lo.v < (short)dep2.lo.v;
			dest->lo.origin =
				expr_b(expr_and(expr_add(dep1.lo.origin,
							 expr_const(0x8000)),
						expr_const(0xffff)),
				       expr_and(expr_add(dep2.lo.origin,
							 expr_const(0x8000)),
						expr_const(0xffff)));
			break;
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (long)dep1.lo.v < (long)dep2.lo.v;
			dest->lo.origin = expr_le(dep1.lo.origin, dep2.lo.origin);
			break;
		default:
			VG_(printf)("Strange operation code %ld for s\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	default:
		VG_(printf)("Strange cond code %ld (op %ld)\n", condcode.lo.v, op.lo.v);
		VG_(tool_panic)((Char *)"failed");
	}

	if (inv) {
		dest->lo.v ^= 1;
		dest->lo.origin = expr_not(dest->lo.origin);
	}
}

static void
do_ccall_calculate_rflags_c(struct interpret_state *state,
			    struct expression_result *dest,
			    IRCallee *cee,
			    IRType retty,
			    IRExpr **args)
{
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(state, &op, args[0]);

	eval_expression(state, &dep1, args[1]);
	eval_expression(state, &dep2, args[2]);
	eval_expression(state, &ndep, args[3]);

	switch (op.lo.v) {
	case AMD64G_CC_OP_INCB:
	case AMD64G_CC_OP_INCW:
	case AMD64G_CC_OP_INCL:
	case AMD64G_CC_OP_INCQ:
	case AMD64G_CC_OP_DECB:
	case AMD64G_CC_OP_DECW:
	case AMD64G_CC_OP_DECL:
	case AMD64G_CC_OP_DECQ:
		dest->lo.v = ndep.lo.v & 1;
		dest->lo.origin = expr_and(ndep.lo.origin, expr_const(1));
		break;

	case AMD64G_CC_OP_SUBB:
		dest->lo.v = (unsigned char)dep1.lo.v < (unsigned char)dep2.lo.v;
		dest->lo.origin = expr_b(expr_and(dep1.lo.origin,
						  expr_const(0xff)),
					 expr_and(dep2.lo.origin,
						  expr_const(0xff)));
		break;

	case AMD64G_CC_OP_SUBL:
		dest->lo.v = (unsigned)dep1.lo.v < (unsigned)dep2.lo.v;
		dest->lo.origin = expr_b(expr_and(dep1.lo.origin,
						  expr_const(0xffffffff)),
					 expr_and(dep2.lo.origin,
						  expr_const(0xffffffff)));
		break;

	case AMD64G_CC_OP_SUBQ:
		dest->lo.v = dep1.lo.v  < dep2.lo.v;
		dest->lo.origin = expr_b(dep1.lo.origin,
					 dep2.lo.origin);
		break;

	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICW:
	case AMD64G_CC_OP_LOGICL:
	case AMD64G_CC_OP_LOGICQ:
		/* XXX Why doesn't the Valgrind optimiser remove
		 * these? */
		dest->lo.v = 0;
		dest->lo.origin = expr_const(0);
		break;

	case AMD64G_CC_OP_SHRB:
	case AMD64G_CC_OP_SHRW:
	case AMD64G_CC_OP_SHRL:
	case AMD64G_CC_OP_SHRQ:
		dest->lo.v = dep2.lo.v & 1;
		dest->lo.origin = expr_and(dep1.lo.origin, expr_const(1));
		break;

	default:
		VG_(printf)("Can't calculate C flags for op %ld\n",
			    op.lo.v);
		VG_(tool_panic)((Char *)"dead");
	}
}

static void
do_ccall_generic(struct interpret_state *state, struct expression_result *dest,
		 IRCallee *cee, IRType retty, IRExpr **args)
{
	struct expression_result rargs[6];
	unsigned x;

	tl_assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(state, &rargs[x], args[x]);
	}
	dest->lo.v = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				       unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].lo.v, rargs[1].lo.v, rargs[2].lo.v, rargs[3].lo.v, rargs[4].lo.v,
		 rargs[5].lo.v);
	dest->hi.v = 0;
	dest->hi.origin = NULL;
	dest->lo.origin = rargs[0].lo.origin;
	for (x = 1; args[x]; x++)
		dest->lo.origin = expr_combine(dest->lo.origin, rargs[x].lo.origin);
}

static void
do_ccall(struct interpret_state *state,
	 struct expression_result *dest,
	 IRCallee *cee,
	 IRType retty,
	 IRExpr **args)
{
	if (!VG_(strcmp)((Char *)cee->name, (Char *)"amd64g_calculate_condition")) {
		do_ccall_calculate_condition(state, dest, cee, retty, args);
	} else if (!VG_(strcmp)((Char *)cee->name, (Char *)"amd64g_calculate_rflags_c")) {
		do_ccall_calculate_rflags_c(state, dest, cee, retty, args);
	} else {
		do_ccall_generic(state, dest, cee, retty, args);
	}
}

static void
eval_expression(struct interpret_state *state,
		struct expression_result *dest,
		IRExpr *expr)
{
#define ORIGIN(x)				\
	do {					\
		dest->lo.origin = x;		\
	} while (0)

	tl_assert(expr != NULL);
	dest->lo.v = 0xdeadbeeff001f001;
	dest->lo.origin = NULL;
	dest->hi.v = 0xaaaaaaaaaaaaaaaa;
	dest->hi.origin = NULL;

	switch (expr->tag) {
	case Iex_Get: {
		unsigned long v1;
		const struct expression *src1;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src1 = read_reg(state,
				expr->Iex.Get.offset - sub_word_offset,
				&v1);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			dest->lo.origin = src1;
			break;
		case Ity_V128:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			dest->lo.origin = src1;
			dest->hi.origin = read_reg(state,
						   expr->Iex.Get.offset - sub_word_offset,
						   &dest->hi.v);
			break;
		case Ity_I32:
			tl_assert(!(sub_word_offset % 4));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffffffff;
			dest->lo.origin = expr_and(expr_const(0xffffffff),
						   expr_shrl(src1,
							     expr_const(sub_word_offset * 8)));
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffff;
			dest->lo.origin = expr_and(expr_const(0xffff),
						   expr_shrl(src1,
							     expr_const(sub_word_offset * 8)));
			break;
		case Ity_I8:
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xff;
			dest->lo.origin = expr_and(expr_const(0xff),
						   expr_shrl(src1,
							     expr_const(sub_word_offset * 8)));
			break;
		default:
			VG_(tool_panic)((Char *)"bad get type");
		}
		break;
	}

	case Iex_RdTmp:
		*dest = state->temporaries[expr->Iex.RdTmp.tmp];
		break;

	case Iex_Const: {
		IRConst *cnst = expr->Iex.Const.con;
		dest->lo.origin = NULL;
		dest->hi.origin = NULL;
		switch (cnst->tag) {
		case Ico_U1:
			dest->lo.v = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->lo.v = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->lo.v = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->lo.v = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo.v = cnst->Ico.U64;
			break;
		case Ico_V128:
			dest->lo.v = cnst->Ico.V128;
			dest->lo.v = dest->lo.v | (dest->lo.v << 16) | (dest->lo.v << 32) | (dest->lo.v << 48);
			dest->hi.v = dest->lo.v;
			dest->hi.origin = expr_const(dest->hi.v);
			break;
		default:
			ASSUME(0);
		}
		dest->lo.origin = expr_const(dest->lo.v);
		break;
	}

	case Iex_Binop: {
		struct expression_result arg1;
		struct expression_result arg2;
		eval_expression(state, &arg1, expr->Iex.Binop.arg1);
		eval_expression(state, &arg2, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			dest->lo.v = arg1.lo.v - arg2.lo.v;
			ORIGIN(expr_sub(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sub32:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Sub8:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xff)));
			break;
		case Iop_Add64:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			ORIGIN(expr_add(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Add64x2:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			dest->hi.v = arg1.hi.v + arg2.hi.v;
			dest->lo.origin = expr_add(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_add(arg1.hi.origin, arg2.hi.origin);
			break;
		case Iop_Add32:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_add(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And8:
			dest->lo.v = arg1.lo.v & arg2.lo.v;
			ORIGIN(expr_and(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Or8:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo.v = arg1.lo.v | arg2.lo.v;
			ORIGIN(expr_or(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shl32:
			dest->lo.v = (arg1.lo.v << arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_shl(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Shl64:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			ORIGIN(expr_shl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sar64:
			dest->lo.v = (long)arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shra(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shr64:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shrl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Xor64:
		case Iop_Xor32:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
			ORIGIN(expr_xor(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE8:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo.v = arg1.lo.v == arg2.lo.v;
			ORIGIN(expr_eq(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpLE64U:
			dest->lo.v = arg1.lo.v <= arg2.lo.v;
			ORIGIN(expr_be(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLE64S:
			dest->lo.v = (long)arg1.lo.v <= (long)arg2.lo.v;
			ORIGIN(expr_le(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLT64S:
			dest->lo.v = (long)arg1.lo.v < (long)arg2.lo.v;
			ORIGIN(expr_and(expr_le(arg1.lo.origin, arg2.lo.origin),
					expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin))));
			break;
		case Iop_CmpLT64U:
			dest->lo.v = arg1.lo.v < arg2.lo.v;
			ORIGIN(expr_b(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Mul64:
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			ORIGIN(expr_mul(arg1.lo.origin, arg2.lo.origin));
			break;

		case Iop_MullU32: {
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			dest->lo.origin = expr_mul(arg1.lo.origin, arg2.lo.origin);
			break;
		}
		case Iop_MullS32: {
			dest->lo.v = (long)(int)arg1.lo.v * (long)(int)arg2.lo.v;
			dest->lo.origin = expr_muls(expr_shra(expr_shl(arg1.lo.origin,
								       expr_const(32)),
							      expr_const(32)),
						    expr_shra(expr_shl(arg2.lo.origin,
								       expr_const(32)),
							      expr_const(32)));
			break;
		}

		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			a1 = arg1.lo.v & 0xffffffff;
			a2 = arg1.lo.v >> 32;
			b1 = arg2.lo.v & 0xffffffff;
			b2 = arg2.lo.v >> 32;
			dest->hi.v = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32)) >> 32);
			dest->lo.origin = expr_mul(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_mul_hi(arg1.lo.origin, arg2.lo.origin);
			break;
		}
		case Iop_32HLto64:
			dest->lo.v = (arg1.lo.v << 32) | arg2.lo.v;
			ORIGIN(expr_or(expr_shl(arg1.lo.origin,
						expr_const(32)),
				       arg2.lo.origin));
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			dest->lo.origin = arg2.lo.origin;
			dest->hi.origin = arg1.lo.origin;
			break;

		case Iop_DivModU64to32:
			dest->lo.v = (arg1.lo.v / arg2.lo.v) |
				((arg1.lo.v % arg2.lo.v) << 32);
			dest->lo.origin = expr_combine(arg1.lo.origin,
						       arg2.lo.origin);
			break;

		case Iop_DivModU128to64:
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			asm ("div %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			dest->lo.origin = expr_combine(arg1.lo.origin,
						       expr_combine(arg1.hi.origin,
								    arg2.lo.origin));
			dest->hi.origin = dest->lo.origin;
			break;

		case Iop_DivModS128to64:
			asm ("idiv %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			dest->lo.origin = expr_combine(arg1.lo.origin,
						       expr_combine(arg1.hi.origin,
								    arg2.lo.origin));
			dest->hi.origin = dest->lo.origin;
			break;

		case Iop_Add32x4:
			dest->lo.v = ((arg1.lo.v + arg2.lo.v) & 0xffffffff) +
				((arg1.lo.v & ~0xfffffffful) + (arg2.lo.v & ~0xfffffffful));
			dest->hi.v = ((arg1.hi.v + arg2.hi.v) & 0xffffffff) +
				((arg1.hi.v & ~0xfffffffful) + (arg2.hi.v & ~0xfffffffful));
			dest->lo.origin = expr_combine(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_combine(arg1.hi.origin, arg2.hi.origin);
			break;

		case Iop_InterleaveLO64x2:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			dest->lo.origin = arg2.lo.origin;
			dest->hi.origin = arg1.lo.origin;
			break;

		case Iop_InterleaveHI64x2:
			dest->lo.v = arg2.hi.v;
			dest->hi.v = arg1.hi.v;
			dest->lo.origin = arg2.hi.origin;
			dest->hi.origin = arg1.hi.origin;
			break;

		case Iop_InterleaveLO32x4:
			dest->lo.v = (arg2.lo.v & 0xffffffff) | (arg1.lo.v << 32);
			dest->hi.v = (arg2.lo.v >> 32) | (arg1.lo.v & 0xffffffff00000000ul);
			dest->lo.origin = expr_or(expr_and(arg2.lo.origin,
							   expr_const(0xffffffff)),
						  expr_shl(arg1.lo.origin,
							   expr_const(32)));
			dest->hi.origin = expr_or(expr_shrl(arg2.lo.origin,
							    expr_const(32)),
						  expr_and(arg1.lo.origin,
							   expr_const(0xffffffff00000000ul)));
			break;

		case Iop_InterleaveHI32x4:
			dest->lo.v = (arg2.hi.v & 0xffffffff) | (arg1.hi.v << 32);
			dest->hi.v = (arg2.hi.v >> 32) | (arg1.hi.v & 0xffffffff00000000ul);
			dest->lo.origin = expr_or(expr_and(arg2.hi.origin,
							   expr_const(0xffffffff)),
						  expr_shl(arg1.hi.origin,
							   expr_const(32)));
			dest->hi.origin = expr_or(expr_shrl(arg2.hi.origin,
							    expr_const(32)),
						  expr_and(arg1.hi.origin,
							   expr_const(0xffffffff00000000ul)));
			break;

		case Iop_ShrN64x2:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			dest->hi.v = arg1.hi.v >> arg2.lo.v;
			dest->lo.origin = expr_shrl(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_shrl(arg1.hi.origin, arg2.lo.origin);
			break;

		case Iop_ShlN64x2:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			dest->hi.v = arg1.hi.v << arg2.lo.v;
			dest->lo.origin = expr_shl(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_shl(arg1.hi.origin, arg2.lo.origin);
			break;

		case Iop_CmpGT32Sx4:
			dest->lo.v = 0;
			dest->hi.v = 0;
			if ( (int)arg1.lo.v > (int)arg2.lo.v )
				dest->lo.v |= 0xffffffff;
			if ( (int)(arg1.lo.v >> 32) > (int)(arg2.lo.v >> 32) )
				dest->lo.v |= 0xffffffff00000000;
			if ( (int)arg1.hi.v > (int)arg2.hi.v )
				dest->hi.v |= 0xffffffff;
			if ( (int)(arg1.hi.v >> 32) > (int)(arg2.hi.v >> 32) )
				dest->hi.v |= 0xffffffff00000000;
			dest->lo.origin = expr_combine(arg1.lo.origin, arg2.lo.origin);
			dest->hi.origin = expr_combine(arg1.hi.origin, arg2.hi.origin);
			break;

		default:
			VG_(tool_panic)((Char *)"bad binop");
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg;
		eval_expression(state, &arg, expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo.v = arg.lo.v >> 32;
			ORIGIN(expr_shrl(arg.lo.origin, expr_const(32)));
			break;
		case Iop_64to32:
			dest->lo.v = arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xfffffffful)));
			break;
		case Iop_64to16:
			dest->lo.v = arg.lo.v & 0xffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xffff)));
			break;
		case Iop_64to8:
			dest->lo.v = arg.lo.v & 0xff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xff)));
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo.v = arg.lo.v;
			ORIGIN(arg.lo.origin);
			break;
		case Iop_64to1:
			dest->lo.v = arg.lo.v & 1;
			ORIGIN(expr_and(arg.lo.origin, expr_const(1)));
			break;
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_16Uto32:
		case Iop_1Uto64:
		case Iop_1Uto8:
		case Iop_8Uto32:
		case Iop_8Uto64:
			*dest = arg;
			break;
		case Iop_32Sto64:
			dest->lo.v = (long)(int)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(32)),
					 expr_const(32)));
			break;
		case Iop_8Sto64:
			dest->lo.v = (long)(signed char)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(56)),
					 expr_const(56)));
			break;
		case Iop_8Sto32:
			dest->lo.v = (int)(signed char)arg.lo.v;
			ORIGIN(expr_and(expr_shra(expr_shl(arg.lo.origin,
							   expr_const(56)),
						  expr_const(56)),
					expr_const(0xffffffff)));
			break;
		case Iop_16Sto64:
			dest->lo.v = (long)(short)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(48)),
					 expr_const(48)));
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo.v = arg.hi.v;
			tl_assert(arg.hi.origin != NULL);
			ORIGIN(arg.hi.origin);
			break;

		case Iop_Not1:
			dest->lo.v = !arg.lo.v;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(1)));
			break;

		case Iop_Not32:
			dest->lo.v = ~arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(0xffffffff)));
			break;

		case Iop_Not64:
			dest->lo.v = ~arg.lo.v;
			ORIGIN(expr_not(arg.lo.origin));
			break;

		default:
			VG_(tool_panic)((Char *)"bad unop");
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result cond;
		struct expression_result res0;
		struct expression_result resX;
		struct expression_result *choice;
		eval_expression(state, &cond, expr->Iex.Mux0X.cond);
		tl_assert(!cond.hi.origin);
		eval_expression(state, &res0, expr->Iex.Mux0X.expr0);
		eval_expression(state, &resX, expr->Iex.Mux0X.exprX);
		if (cond.lo.v == 0) {
			choice = &res0;
		} else {
			choice = &resX;
		}
		*dest = *choice;
		dest->lo.origin = expr_combine(cond.lo.origin, choice->lo.origin);
		if (choice->hi.origin)
			dest->hi.origin = expr_combine(cond.lo.origin, choice->hi.origin);
		else
			dest->hi.origin = NULL;
		break;
	}

	case Iex_CCall: {
		do_ccall(state, dest, expr->Iex.CCall.cee,
			 expr->Iex.CCall.retty, expr->Iex.CCall.args);
		break;
	}

	default:
		VG_(printf)("Bad expression tag %x\n", expr->tag);
		VG_(tool_panic)((Char *)"failed2");
	}
#undef ORIGIN
}

static struct expression_result
do_helper_load_cswitch(struct interpret_state *is,
		       unsigned size,
		       struct abstract_interpret_value addr,
		       struct abstract_interpret_value rsp)
{
	struct expression_result res;
	unsigned char dummy_buf[16];

	interpreter_do_load(&res, size, addr);

	ref_expression_result(is, &res);
	load_event((const void *)addr.v, size, dummy_buf, rsp.v);
	deref_expression_result(is, &res);

	return res;
}

static void
do_helper_store_cswitch(unsigned size,
			struct abstract_interpret_value addr,
			struct expression_result data,
			struct abstract_interpret_value rsp)
{
	unsigned long buf[2];

	if (size == 16) {
		interpret_create_mem_lookaside(addr.v, 8, data.lo);
		interpret_create_mem_lookaside(addr.v+8, 8, data.hi);
	} else {
		interpret_create_mem_lookaside(addr.v, size, data.lo);
	}

	buf[0] = data.lo.v;
	buf[1] = data.hi.v;
	store_event((void *)addr.v,
		    size,
		    buf,
		    rsp.v);
}

static struct expression_result
do_helper_cas_cswitch(struct interpret_state *is,
		      unsigned size,
		      struct abstract_interpret_value addr,
		      struct expression_result expected,
		      struct expression_result data,
		      struct abstract_interpret_value rsp)
{
	struct expression_result seen;
	struct expression_result new;
	const struct expression *pred;

	seen = do_helper_load_cswitch(is, size, addr, rsp);
	pred = expr_eq(seen.lo.origin, expected.lo.origin);
	if (seen.hi.origin)
		pred = expr_and(pred,
				expr_eq(seen.hi.origin,
					expected.hi.origin));
	if (seen.lo.v == expected.lo.v && seen.hi.v == expected.hi.v) {
		new.lo.v = data.lo.v;
		new.hi.v = data.hi.v;
		new.lo.origin = expr_combine(pred, data.lo.origin);
		if (data.hi.origin)
			new.hi.origin = expr_combine(pred, data.hi.origin);
		else
			new.hi.origin = NULL;

		do_helper_store_cswitch(size,
					addr,
					new,
					rsp);
	} else {
		new.lo.v = seen.lo.v;
		new.hi.v = seen.hi.v;
		new.lo.origin = expr_combine(pred,
					     seen.lo.origin);
		if (seen.hi.origin)
			new.hi.origin = expr_combine(pred, seen.hi.origin);
		else
			new.hi.origin = NULL;

		if (size == 16) {
			interpret_create_mem_lookaside(addr.v, 8, new.lo);
			interpret_create_mem_lookaside(addr.v+8, 8, new.hi);
		} else {
			interpret_create_mem_lookaside(addr.v, size, new.lo);
		}
	}

	return seen;
}

#define strcmp(x, y) VG_(strcmp)((Char *)(x), (Char *)y)

/* XXX We don't track dependencies through dirty calls at all.  Oh
 * well. */
static void
do_dirty_call_cswitch(struct interpret_state *is,
		      VexGuestAMD64State *state,
		      IRSB *irsb,
		      IRDirty *details)
{
	struct expression_result guard;
	struct expression_result args[6];
	unsigned x;
	unsigned long res;

	if (details->guard) {
		eval_expression(is, &guard, details->guard);
		if (!current_thread->in_monitor)
			send_non_const_expression(guard.lo.origin);
		if (!guard.lo.v)
			return;
	}
	for (x = 0; details->args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(is, &args[x], details->args[x]);
	}
	tl_assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "footstep_event")) {
		footstep_event(args[0].lo.v,
			       args[1].lo.v,
			       args[2].lo.v,
			       args[3].lo.v,
			       args[4].lo.v,
			       args[5].lo.v);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		is->temporaries[details->tmp] =
			do_helper_load_cswitch(is, 1, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		is->temporaries[details->tmp] =
			do_helper_load_cswitch(is, 2, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		is->temporaries[details->tmp] =
			do_helper_load_cswitch(is, 4, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		is->temporaries[details->tmp] =
			do_helper_load_cswitch(is, 8, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		is->temporaries[details->tmp] =
			do_helper_load_cswitch(is, 16, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_store_8")) {
		do_helper_store_cswitch(1, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_16")) {
		do_helper_store_cswitch(2, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_32")) {
		do_helper_store_cswitch(4, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_64")) {
		do_helper_store_cswitch(8, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_128")) {
		args[1].hi = args[2].lo;
		do_helper_store_cswitch(16, args[0].lo, args[1], args[3].lo);
	} else if (!strcmp(details->cee->name, "helper_cas_8")) {
		is->temporaries[details->tmp] =
			do_helper_cas_cswitch(is, 1, args[0].lo, args[1], args[2],
					      args[3].lo);
	} else if (!strcmp(details->cee->name, "helper_cas_16")) {
		is->temporaries[details->tmp] =
			do_helper_cas_cswitch(is, 2, args[0].lo, args[1], args[2],
					      args[3].lo);
	} else if (!strcmp(details->cee->name, "helper_cas_32")) {
		is->temporaries[details->tmp] =
			do_helper_cas_cswitch(is, 4, args[0].lo, args[1], args[2],
					      args[3].lo);
	} else if (!strcmp(details->cee->name, "helper_cas_64")) {
		is->temporaries[details->tmp] =
			do_helper_cas_cswitch(is, 8, args[0].lo, args[1], args[2],
					      args[3].lo);
	} else {
		VG_(printf)("Unknown dirty call %s\n", details->cee->name);
		commit_interpreter_state();

		if (details->needsBBP) {
			res = ((unsigned long (*)(VexGuestAMD64State *,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long))(details->cee->addr))
				(state, args[0].lo.v, args[1].lo.v, args[2].lo.v, args[3].lo.v,
				 args[4].lo.v, args[5].lo.v);
		} else {
			res = ((unsigned long (*)(unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long))(details->cee->addr))
				(args[0].lo.v, args[1].lo.v, args[2].lo.v, args[3].lo.v,
				 args[4].lo.v, args[5].lo.v);
		}

		initialise_interpreter_state();

		if (details->tmp != IRTemp_INVALID) {
			is->temporaries[details->tmp].lo.v = res;
			is->temporaries[details->tmp].lo.origin =
				expr_imported(res);
			is->temporaries[details->tmp].hi.v = 0;
			is->temporaries[details->tmp].hi.origin = NULL;
		}
	}
}

UInt
interpret_log_control_flow(VexGuestAMD64State *state)
{
	struct interpret_state *istate = &current_thread->interpret_state;
	VexGuestExtents vge;
	VexArch vex_arch;
	VexArchInfo vex_archinfo;
	VexAbiInfo vex_abiinfo;
	Addr64 addr;
	IRSB *irsb;
	IRStmt *stmt;
	unsigned stmt_nr;

	addr = istate->registers[REG_RIP].v;
	if (addr == 0) {
		/* Hackity hackity hack: at the start of day, RIP in
		   the interpreter state is wrong.  Fix it up a
		   bit. */
		initialise_is_for_vex_state(istate, state);
		addr = state->guest_RIP;
	}

	/* This is all ripped from VG_(translate) and
	 * LibVEX_Translate(). */

	VG_(init_vex)();

	VG_(machine_get_VexArchInfo)(&vex_arch, &vex_archinfo);
	LibVEX_default_VexAbiInfo(&vex_abiinfo);
	vex_abiinfo.guest_stack_redzone_size = VG_STACK_REDZONE_SZB;
	vex_abiinfo.guest_amd64_assume_fs_is_zero  = True;

	vexSetAllocModeTEMP_and_clear();

	irsb = bb_to_IR ( &vge,
			  NULL,
			  disInstr_AMD64,
			  ULong_to_Ptr(addr),
			  (Addr64)addr,
			  chase_into_ok,
			  False,
			  vex_arch,
			  &vex_archinfo,
			  &vex_abiinfo,
			  Ity_I64,
			  0,
			  NULL,
			  offsetof(VexGuestAMD64State, guest_TISTART),
			  offsetof(VexGuestAMD64State, guest_TILEN) );

	irsb = do_iropt_BB (irsb, guest_amd64_spechelper,
			    guest_amd64_state_requires_precise_mem_exns,
			    addr );

	irsb = instrument_func(NULL, irsb, &amd64guest_layout, &vge,
			       Ity_I64, Ity_I64);

	irsb = do_iropt_BB (irsb, guest_amd64_spechelper,
			    guest_amd64_state_requires_precise_mem_exns,
			    addr );

	tl_assert(istate->temporaries == NULL);
	istate->nr_temporaries = irsb->tyenv->types_used;
	istate->temporaries = VG_(malloc)("interpreter temporaries",
					  sizeof(istate->temporaries[0]) *
					  istate->nr_temporaries);
	VG_(memset)(istate->temporaries,
		    0,
		    sizeof(istate->temporaries[0]) *
		    istate->nr_temporaries);
	for (stmt_nr = 0; stmt_nr < irsb->stmts_used; stmt_nr++) {
		stmt = irsb->stmts[stmt_nr];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			break;
		case Ist_MBE:
			break;
		case Ist_WrTmp:
			eval_expression(istate,
					&istate->temporaries[stmt->Ist.WrTmp.tmp],
					stmt->Ist.WrTmp.data);
			break;
		case Ist_Put: {
			unsigned byte_offset = stmt->Ist.Put.offset & 7;
			struct abstract_interpret_value *dest =
				get_aiv_for_offset(istate,
						   stmt->Ist.Put.offset - byte_offset);
			struct expression_result data;

			eval_expression(istate, &data, stmt->Ist.Put.data);
			switch (typeOfIRExpr(irsb->tyenv, stmt->Ist.Put.data)) {
			case Ity_I8:
				dest->v &= ~(0xFF << (byte_offset * 8));
				dest->v |= data.lo.v << (byte_offset * 8);
				dest->origin =
					expr_or( expr_shl(data.lo.origin,
							  expr_const(byte_offset * 8)),
						 expr_and(dest->origin,
							  expr_const(~(0xFF << (byte_offset * 8)))));
				break;

			case Ity_I16:
				tl_assert(!(byte_offset % 2));
				dest->v &= ~(0xFFFF << (byte_offset * 8));
				dest->v |= data.lo.v << (byte_offset * 8);
				dest->origin =
					expr_or( expr_shl(data.lo.origin,
							  expr_const(byte_offset * 8)),
						 expr_and(dest->origin,
							  expr_const(~(0xFFFF << (byte_offset * 8)))));
				break;

			case Ity_I64:
				tl_assert(byte_offset == 0);
				*dest = data.lo;
				break;

			case Ity_I128:
			case Ity_V128:
				tl_assert(byte_offset == 0);
				*dest = data.lo;
				*get_aiv_for_offset(istate,
						    stmt->Ist.Put.offset + 8) =
					data.hi;
				break;
			default:
				VG_(tool_panic)((Char *)"put to strange-sized location");
			}
			break;
		}

		case Ist_Dirty: {
			do_dirty_call_cswitch(istate, state, irsb, stmt->Ist.Dirty.details);
			break;
		}

		case Ist_Exit: {
			struct expression_result guard;
			if (stmt->Ist.Exit.guard) {
				eval_expression(istate, &guard, stmt->Ist.Exit.guard);
				if (!current_thread->in_monitor)
					send_non_const_expression(guard.lo.origin);
				if (!guard.lo.v)
					break;
			}
			tl_assert(stmt->Ist.Exit.jk == Ijk_Boring);
			tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
			istate->registers[REG_RIP].v = stmt->Ist.Exit.dst->Ico.U64;
			goto finished_block;
		}

		default:
			VG_(printf)("Don't know how to interpret statement ");
			ppIRStmt(stmt);
			VG_(tool_panic)((Char *)"death");
			break;
		}
	}

	tl_assert(irsb->jumpkind == Ijk_Boring ||
		  irsb->jumpkind == Ijk_Call ||
		  irsb->jumpkind == Ijk_Ret ||
		  irsb->jumpkind == Ijk_Sys_syscall ||
		  irsb->jumpkind == Ijk_ClientReq);

	{
		struct expression_result next_addr;
		eval_expression(istate, &next_addr, irsb->next);
		tl_assert(next_addr.hi.origin == NULL);
		if (!current_thread->in_monitor)
			send_non_const_expression(next_addr.lo.origin);
		istate->registers[REG_RIP].v = next_addr.lo.v;
	}

	/* Careful: these can force context switches, so any
	   expressions not stored in the interpreter state or to
	   memory might get garbage collected. */
	if (irsb->jumpkind == Ijk_Sys_syscall) {
		commit_interpreter_state();
		syscall_event(state);
		initialise_interpreter_state();
	}

	if (irsb->jumpkind == Ijk_ClientReq) {
		UWord *args;
		args = (UWord *)istate->registers[0].v;
		VG_(in_generated_code) = False;
		client_request_event(current_thread->id,
				     args,
				     &istate->registers[REG_RDX].v);
		VG_(in_generated_code) = True;

		istate->registers[REG_RDX].origin =
			expr_imported(istate->registers[REG_RDX].v);
	}

finished_block:
	VG_(free)(istate->temporaries);
	istate->temporaries = NULL;
	istate->nr_temporaries = 0;

	gc_expressions();

	state->guest_RIP = istate->registers[REG_RIP].v;

	return VG_TRC_BORING;
}

static jmp_buf
disassemble_jmpbuf;

static void
disassemble_sighandler(Int signo, Addr addr)
{
	if (signo == VKI_SIGBUS || signo == VKI_SIGSEGV) {
		/* Something bad has happened, and we can't replay the
		   memory record which we captured.  This shouldn't
		   happen if we follow the script, but it's possible
		   if we've diverged. */
		__builtin_longjmp(disassemble_jmpbuf, 1);
	}
}

void
disassemble_addr(unsigned long addr)
{
	vki_sigset_t sigmask;
	VexGuestExtents vge;
	VexArch vex_arch;
	VexArchInfo vex_archinfo;
	VexAbiInfo vex_abiinfo;
	IRSB *irsb;

	VG_(init_vex)();
	VG_(machine_get_VexArchInfo)(&vex_arch, &vex_archinfo);
	LibVEX_default_VexAbiInfo(&vex_abiinfo);
	vex_abiinfo.guest_stack_redzone_size = VG_STACK_REDZONE_SZB;
	vex_abiinfo.guest_amd64_assume_fs_is_zero  = True;

	vexSetAllocModeTEMP_and_clear();

	if (__builtin_setjmp(&disassemble_jmpbuf)) {
		VG_(set_fault_catcher)(NULL);
		VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
		VG_(printf)("Failed to disassemble from %lx due to signal\n",
			    addr);
		return;
	}
	VG_(sigprocmask)(VKI_SIG_SETMASK, NULL, &sigmask);
	VG_(set_fault_catcher)(disassemble_sighandler);
	irsb = bb_to_IR ( &vge,
			  NULL,
			  disInstr_AMD64,
			  ULong_to_Ptr(addr),
			  (Addr64)addr,
			  chase_into_ok,
			  False,
			  vex_arch,
			  &vex_archinfo,
			  &vex_abiinfo,
			  Ity_I64,
			  0,
			  NULL,
			  offsetof(VexGuestAMD64State, guest_TISTART),
			  offsetof(VexGuestAMD64State, guest_TILEN) );
	VG_(set_fault_catcher)(NULL);
	VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);

	irsb = do_iropt_BB (irsb, guest_amd64_spechelper,
			    guest_amd64_state_requires_precise_mem_exns,
			    addr );

	irsb = instrument_func(NULL, irsb, &amd64guest_layout, &vge,
			       Ity_I64, Ity_I64);

	irsb = do_iropt_BB (irsb, guest_amd64_spechelper,
			    guest_amd64_state_requires_precise_mem_exns,
			    addr );


	ppIRSB(irsb);
}
