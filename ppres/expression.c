/* All the gubbins for manipulating struct expression, including the
   GC */
#include <stddef.h>
#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_tooliface.h"
#include "libvex_guest_amd64.h"

#include "replay.h"
#include "replay2.h"

struct maybe_expression {
	unsigned long in_use_ptr; /* Bottom bit is the in_use flag,
				     next is the mark-and-sweep mark,
				     and the rest is a pointer which
				     can be used by the garbage
				     collector. */
	union {
		struct maybe_expression *next_free;
		struct expression expr;
	} u;
};

#define EXPRESSIONS_PER_ARENA 4096
#define ARENA_MAGIC 0xe5a7ca94cd42fd51
struct expression_arena {
	unsigned long magic;
	struct expression_arena *next, *prev;
	struct maybe_expression exprs[EXPRESSIONS_PER_ARENA];
};

static struct expression_arena *
head_expr_arena;

static struct maybe_expression *
head_free_expression;

static struct expression *
head_constant_expression;

static unsigned
nr_free_expressions,
expressions_in_use,
nr_expression_arenas;

/* ---------------- Predicates on operators ------------------ */
static Bool
op_binop(unsigned x)
{
	return x >= EXPR_BINOP_FIRST && x <= EXPR_BINOP_LAST;
}

static Bool
op_logical(unsigned x)
{
	return x >= EXPR_LOGICAL_FIRST && x <= EXPR_LOGICAL_LAST;
}

static Bool
binop_commutes(unsigned op)
{
	switch (op) {
	case EXPR_AND: case EXPR_OR: case EXPR_EQ: case EXPR_XOR:
	case EXPR_MUL: case EXPR_MUL_HI: case EXPR_COMBINE:
	case EXPR_MULS: case EXPR_ADD:
		return True;
	default:
		return False;
	}
}

/* True if 0 {op} x == x (i.e. if 0 is a left identity for op) */
static Bool
binop_lident_0(unsigned op)
{
	switch (op) {
	case EXPR_OR: case EXPR_ADD: case EXPR_XOR:
		return True;
	default:
		return False;
	}
}

/* True if x {op} 0 == x (i.e. if 0 is a right identity for op) */
static Bool
binop_rident_0(unsigned op)
{
	switch (op) {
	case EXPR_OR: case EXPR_ADD: case EXPR_XOR: case EXPR_SUB:
	case EXPR_SHRL: case EXPR_SHL: case EXPR_SHRA:
		return True;
	default:
		return False;
	}
}

/* Can a {op} (b {op} c) be safely rewritten to (a {op} b) {op} c? */
static Bool
binop_associates(unsigned op)
{
	switch (op) {
	case EXPR_AND: case EXPR_COMBINE: case EXPR_OR: case EXPR_ADD:
	case EXPR_XOR:
		return True;
	default:
		return False;
	}
}




/* ------------------ The garbage collector ------------------------ */

static Bool
gc_discover_expression(const struct expression *e)
{
	struct maybe_expression *me =
		(struct maybe_expression *)((unsigned long *)e - 1);
	Bool res;
	tl_assert(e == &me->u.expr);
	res = !!(me->in_use_ptr & 2);
	me->in_use_ptr |= 2;
	return res;
}

/* XXX TODO: use the pointer flipping trick to reduce stack usage. */
static void
gc_explore_expression(const struct expression *e)
{
	if (!e)
		return;

	if (gc_discover_expression(e))
		return;

	expressions_in_use++;
	if (op_binop(e->type)) {
		gc_explore_expression(e->u.binop.arg1);
		gc_explore_expression(e->u.binop.arg2);
		return;
	} else {
		switch (e->type) {
		case EXPR_CONST:
		case EXPR_IMPORTED:
		case EXPR_REG:
			break;
		case EXPR_MEM:
			gc_explore_expression(e->u.mem.ptr_e);
			gc_explore_expression(e->u.mem.val);
			return;
		case EXPR_NOT:
			gc_explore_expression(e->u.unop.e);
			return;
		default:
			VG_(tool_panic)((Char *)"gc exploration hit bad expression type");
		}
	}
}

static void
gc_explore_aiv(const struct abstract_interpret_value *aiv)
{
	gc_explore_expression(aiv->origin);
}

static void
gc_explore_interpret_state(const struct interpret_state *is)
{
	unsigned x;

	gc_explore_expression(is->hazard[0]);
	gc_explore_expression(is->hazard[1]);

	for (x = 0; x < is->nr_temporaries; x++) {
		gc_explore_aiv(&is->temporaries[x].lo);
		gc_explore_aiv(&is->temporaries[x].hi);
	}
	for (x = 0; x <= REG_LAST; x++)
		gc_explore_aiv(&is->registers[x]);
}

static void
gc_explore_mem_lookaside(void)
{
	struct interpret_mem_lookaside *iml;
	for (iml = head_interpret_mem_lookaside; iml; iml = iml->next)
		gc_explore_aiv(&iml->aiv);
}

/* Perform cleanup when an expression gets garbage collected */
static void
finalise_expression(struct expression *e)
{
	if (e->type != EXPR_CONST)
		return;

	/* Remove it from the constant pool */
	if (e->u.cnst.prev) {
		e->u.cnst.prev->u.cnst.next = e->u.cnst.next;
	} else {
		tl_assert(e == head_constant_expression);
		head_constant_expression = e->u.cnst.next;
	}
	if (e->u.cnst.next)
		e->u.cnst.next->u.cnst.prev = e->u.cnst.prev;
}

void
gc_expressions(void)
{
	static unsigned nr_garbage_collections;
	struct maybe_expression *head;
	struct expression_arena *a, *next;
	struct replay_thread *rt;
	int x;
	Bool arena_free;

	if ((++nr_garbage_collections) % 16)
		return;

	/* Clear the mark flag */
	for (a = head_expr_arena; a; a = a->next) {
		tl_assert(a->magic == ARENA_MAGIC);
		for (x = 0; x < EXPRESSIONS_PER_ARENA; x++)
			a->exprs[x].in_use_ptr &= ~2;
	}

	/* Sweep from all roots. */
	expressions_in_use = 0;
	for (rt = head_thread; rt; rt = rt->next)
		gc_explore_interpret_state(&rt->interpret_state);
	gc_explore_mem_lookaside();

	/* Go back and rebuild the free lists. */
	head_free_expression = NULL;
	nr_free_expressions = 0;
	for (a = head_expr_arena; a; a = next) {
		tl_assert(a->magic == ARENA_MAGIC);
		arena_free = True;
		head = head_free_expression;
		for (x = EXPRESSIONS_PER_ARENA - 1; x >= 0; x--) {
			if (!(a->exprs[x].in_use_ptr & 2)) {
				if (a->exprs[x].in_use_ptr & 1) {
					/* This expression just went
					 * from in use to not in
					 * use. */
					finalise_expression(&a->exprs[x].u.expr);
					a->exprs[x].in_use_ptr &= ~1;
				}
				a->exprs[x].u.next_free = head;
				head = &a->exprs[x];
				nr_free_expressions++;
			} else {
				arena_free = False;
			}
		}
		next = a->next;
		if (arena_free) {
			if (a->prev)
				a->prev->next = a->next;
			if (a->next)
				a->next->prev = a->prev;
			if (a == head_expr_arena)
				head_expr_arena = a->next;
			a->magic++;
			nr_free_expressions -= EXPRESSIONS_PER_ARENA;
			nr_expression_arenas--;
			VG_(free)(a);
		} else {
			head_free_expression = head;
		}
	}
}

static struct expression_arena *
_new_expression_arena(void)
{
	struct expression_arena *work;
	unsigned x;

	work = VG_(malloc)("Expression arena", sizeof(*work));
	for (x = 0; x < EXPRESSIONS_PER_ARENA; x++) {
		work->exprs[x].in_use_ptr = 0;
		work->exprs[x].u.next_free = &work->exprs[x+1];
	}
	work->exprs[x-1].u.next_free = head_free_expression;
	head_free_expression = &work->exprs[0];
	work->prev = NULL;
	work->next = head_expr_arena;
	if (head_expr_arena)
		head_expr_arena->prev = work;
	head_expr_arena = work;
	work->magic = ARENA_MAGIC;
	nr_expression_arenas++;
	return work;
}

/* -------------------------- Expression constructors ---------------------- */
static struct expression *
_new_expression(unsigned code)
{
	struct maybe_expression *e;

	if (!head_free_expression)
		_new_expression_arena();
	tl_assert(head_free_expression);
	e = head_free_expression;

	tl_assert(!(e->in_use_ptr & 1));
	e->in_use_ptr |= 1;
	head_free_expression = e->u.next_free;

	VG_(memset)(&e->u.expr, 0, sizeof(e->u.expr));
	e->u.expr.type = code;
	return &e->u.expr;
}

const struct expression *
expr_reg(unsigned reg, unsigned long val)
{
	struct expression *e;
	e = _new_expression(EXPR_REG);
	e->u.reg.name = reg;
	e->u.reg.val = val;
	return e;
}

const struct expression *
expr_const(unsigned long c)
{
	struct expression *e;
	for (e = head_constant_expression; e && e->u.cnst.val != c; e = e->u.cnst.next)
		;
	if (!e) {
		e = _new_expression(EXPR_CONST);
		e->u.cnst.val = c;
		e->u.cnst.prev = NULL;
		e->u.cnst.next = NULL;
	}

	if (e != head_constant_expression) {
		if (e->u.cnst.prev)
			e->u.cnst.prev->u.cnst.next = e->u.cnst.next;
		if (e->u.cnst.next)
			e->u.cnst.next->u.cnst.prev = e->u.cnst.prev;
		e->u.cnst.prev = NULL;
		e->u.cnst.next = head_constant_expression;
		if (head_constant_expression)
			head_constant_expression->u.cnst.prev = e;
		head_constant_expression = e;
	}
	return e;
}

const struct expression *
expr_mem(unsigned size, const struct expression *ptr, const struct expression *val)
{
	struct expression *e;
	e = _new_expression(EXPR_MEM);
	e->u.mem.size = size;
	e->u.mem.ptr_e = ptr;
	e->u.mem.val = val;
	e->u.mem.when = now;
	return e;
}

const struct expression *
expr_not(const struct expression *e)
{
	struct expression *r;
	r = _new_expression(EXPR_NOT);
	r->u.unop.e = e;
	return r;
}

const struct expression *
expr_imported(unsigned long val)
{
	struct expression *e = _new_expression(EXPR_IMPORTED);
	e->u.imported.val = val;
	return e;
}

static const struct expression *
expr_binop(const struct expression *e1, const struct expression *e2, unsigned op)
{
	struct expression *e;
	const struct expression *ec;

	/* + is a little easier to deal with than -.  If we get x -
	   {const}, turn it into x + -{const} */
	if (op == EXPR_SUB && e2->type == EXPR_CONST) {
		e2 = expr_const(-e2->u.cnst.val);
		op = EXPR_ADD;
	}

	if (e1->type == EXPR_CONST && e2->type == EXPR_CONST) {
		/* Try to do some constant folding.  We only do this
		   for a few special cases. */
		switch (op) {
		case EXPR_ADD:
			return expr_const(e1->u.cnst.val + e2->u.cnst.val);
		case EXPR_AND:
			return expr_const(e1->u.cnst.val & e2->u.cnst.val);
		case EXPR_OR:
			return expr_const(e1->u.cnst.val | e2->u.cnst.val);
		case EXPR_XOR:
			return expr_const(e1->u.cnst.val ^ e2->u.cnst.val);
		case EXPR_EQ:
			return expr_const(e1->u.cnst.val == e2->u.cnst.val);
		default:
			break;
		}
	}

	if (op == EXPR_SUB &&
	    e1->type == EXPR_SUB &&
	    e1->u.binop.arg2->type == EXPR_CONST &&
	    e2->type == EXPR_CONST) {
		/* Special case: (x - y) - z -> x - (y + z) if both y
		   and z are constants. */
		e2 = expr_const(e1->u.binop.arg2->u.cnst.val -
				e2->u.cnst.val);
		e1 = e1->u.binop.arg1;
	}

	/* Do some basic canonicalisations first: if the operation is
	   commutative, the thing on the left always has a lower code
	   than the thing on the right. */
	if (binop_commutes(op) &&
	    e1->type > e2->type) {
		ec = e1;
		e1 = e2;
		e2 = ec;
	}
	/* Try to get things with lower codes to the bottom-left of
	   the expression tree (assuming the operation associates).
	   This means rewriting a + (b + c) to (a + b) + c if a's type
	   is less than +'s.  Since we've already arranged that b's
	   type is less than c's (assuming it commutes), this means
	   that types ascend left-to-right and top-to-bottom. */
	if (binop_associates(op) &&
	    e1->type < op &&
	    e2->type == op) {
		e1 = expr_binop(e1, e2->u.binop.arg1, op);
		e2 = e2->u.binop.arg2;
	}
	if (binop_commutes(op) &&
	    e1->type > e2->type) {
		ec = e1;
		e1 = e2;
		e2 = ec;
		tl_assert(e1->type < e2->type);
	}

	/* Special case: 1 & foo is just foo if foo's op is guaranteed
	   to return 0 or 1. */
	if (op == EXPR_AND && e1->type == EXPR_CONST && e1->u.cnst.val == 1 &&
	    op_logical(e2->type))
		return e2;

	if (binop_lident_0(op) &&
	    e1->type == EXPR_CONST &&
	    e1->u.cnst.val == 0) {
		return e2;
	}
	if (binop_rident_0(op) &&
	    e2->type == EXPR_CONST &&
	    e2->u.cnst.val == 0) {
		return e1;
	}
	e = _new_expression(op);
	e->u.binop.arg1 = e1;
	e->u.binop.arg2 = e2;
	return e;
}

#define mk_expr(name1, name2)						\
	const struct expression *					\
	expr_ ## name1 (const struct expression *e1,			\
			const struct expression *e2)			\
	{								\
		return expr_binop(e1, e2, EXPR_ ## name2);		\
	}
mk_expr(sub, SUB)
mk_expr(add, ADD)
mk_expr(mul, MUL)
mk_expr(mul_hi, MUL_HI)
mk_expr(muls, MULS)
mk_expr(and, AND)
mk_expr(or, OR)
mk_expr(xor, XOR)
mk_expr(shrl, SHRL)
mk_expr(shra, SHRA)
mk_expr(shl, SHL)
mk_expr(combine, COMBINE)
mk_expr(le, LE)
mk_expr(be, BE)
mk_expr(eq, EQ)
mk_expr(b, B)


void
send_expression(const struct expression *e)
{
#define expr(...) send_ancillary(ANCILLARY_EXPRESSION, e->type , ## __VA_ARGS__ )
	if (op_binop(e->type)) {
		expr();
		send_expression(e->u.binop.arg1);
		send_expression(e->u.binop.arg2);
	} else {
		switch (e->type) {
		case EXPR_CONST:
			expr(e->u.cnst.val);
			break;
		case EXPR_REG:
			expr(e->u.reg.name, e->u.reg.val);
			break;
		case EXPR_MEM:
			expr(e->u.mem.size, e->u.mem.when.epoch_nr, e->u.mem.when.access_nr);
			send_expression(e->u.mem.ptr_e);
			send_expression(e->u.mem.val);
			break;
		case EXPR_IMPORTED:
			expr(e->u.imported.val);
			break;
		case EXPR_NOT:
			expr();
			send_expression(e->u.unop.e);
			break;
		default:
			VG_(tool_panic)((Char *)"send bad expression");
		}
	}
#undef expr
}

void
send_non_const_expression(const struct expression *e)
{
	if (e->type != EXPR_CONST)
		send_expression(e);
}

void
ref_expression_result(struct interpret_state *is,
		      const struct expression_result *er)
{
	tl_assert(!is->hazard[0]);
	tl_assert(!is->hazard[1]);
	is->hazard[0] = er->lo.origin;
	is->hazard[1] = er->hi.origin;
}

void
deref_expression_result(struct interpret_state *is,
			const struct expression_result *er)
{
	tl_assert(is->hazard[0] == er->lo.origin);
	tl_assert(is->hazard[1] == er->hi.origin);
	is->hazard[0] = NULL;
	is->hazard[1] = NULL;
}
