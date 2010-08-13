#include <assert.h>
#include <setjmp.h>

#include <libvex.h>
#include <libvex_guest_amd64.h>
#include <pub_tool_basics.h>
#include <pub_tool_tooliface.h>
#include <pub_tool_libcbase.h>
#include <pub_tool_libcassert.h>
#include <pub_tool_libcprint.h>
#include <pub_tool_vki.h>

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"
#include "../VEX/priv/main_util.h"
#include "../coregrind/pub_core_dispatch_asm.h"
#include "../coregrind/pub_core_threadstate.h"

typedef struct vki_sigaction_base sigaction_t;

#include "ppres.h"

//#define DBG VG_(printf)
#define DBG(x, ...) do {} while (0)

extern UInt VG_(dispatch_ctr);

/* For some reason, Valgrind provides strcmp() with a slightly
   different API to the normal one.  Sigh. */
static int strcmp(const char *a, const char *b)
{
	return VG_(strcmp)((Char *)a, (Char *)b);
}
#define memcpy VG_(memcpy)
#define memcmp VG_(memcmp)

typedef struct {
	unsigned long long a;
	unsigned long long b;
} ultralong_t;
typedef unsigned long ait;
struct expression_result {
	ait lo;
	ait hi;
};

struct interpret_state {
	VexGuestAMD64State *regs;
	struct expression_result *temporaries;
	IRSB *currentIRSB;
	unsigned currentIRSBOffset;
};

ULong record_rdtsc(void);
unsigned char helper_load_8(const unsigned char *, unsigned long, unsigned long);
void helper_store_8(const unsigned char *, unsigned char, unsigned long, unsigned long);
unsigned short helper_load_16(const unsigned short *, unsigned long, unsigned long);
void helper_store_16(const unsigned short *, unsigned short, unsigned long, unsigned long);
unsigned int helper_load_32(const unsigned int *, unsigned long, unsigned long);
void helper_store_32(const unsigned int *, unsigned int, unsigned long, unsigned long);
unsigned long helper_load_64(const unsigned long *, unsigned long, unsigned long);
void helper_store_64(const unsigned long *, unsigned long, unsigned long, unsigned long);
ultralong_t helper_load_128(const ultralong_t *, unsigned long, unsigned long);
void helper_store_128(const ultralong_t *, ultralong_t, unsigned long, unsigned long);

unsigned int helper_cas_32(unsigned int *, unsigned int, unsigned int, unsigned long, unsigned long);
unsigned long helper_cas_64(unsigned long *, unsigned long, unsigned long, unsigned long, unsigned long);

void typeOfPrimop ( IROp op, 
                    /*OUTs*/
                    IRType* t_dst, 
                    IRType* t_arg1, IRType* t_arg2, 
                    IRType* t_arg3, IRType* t_arg4 );

static struct expression_result eval_expression(struct interpret_state *is, IRExpr *expr);

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

#define REG_LAST 128

static void
write_reg(VexGuestAMD64State *state, unsigned offset, ait val)
{
	tl_assert(!(offset % 8));
	((ait *)state)[offset /8] = val;
}

static ait
read_reg(VexGuestAMD64State *state, unsigned offset)
{
	tl_assert(!(offset % 8));
	return ((ait *)state)[offset / 8];
}

#define REGISTER_IDX(x) (offsetof(VexGuestAMD64State, guest_ ## x) / 8)
#define force(x) (x)
#define mkConst(x) (x ## ul)
#define sanity_check_ait(x)

static void
my_amd64g_dirtyhelper_CPUID_sse3_and_cx16(VexGuestAMD64State *regs)
{
#define SET_ABCD(_a,_b,_c,_d)						\
	do {								\
		regs->guest_RAX = _a;					\
		regs->guest_RBX = _b;					\
		regs->guest_RCX = _c;					\
		regs->guest_RDX = _d;					\
	} while (0)

	switch (force(mkConst(0xFFFFFFFF) & regs->guest_RAX)) {
	case 0x00000000:
		SET_ABCD(0x0000000a, 0x756e6547, 0x6c65746e, 0x49656e69);
		break;
	case 0x00000001:
		SET_ABCD(0x000006f6, 0x00020800, 0x0000e3bd, 0xbfebfbff);
		break;
	case 0x00000002:
		SET_ABCD(0x05b0b101, 0x005657f0, 0x00000000, 0x2cb43049);
		break;
	case 0x00000003:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000004: {
		switch (force(mkConst(0xFFFFFFFF) & regs->guest_RCX)) {
		case 0x00000000: SET_ABCD(0x04000121, 0x01c0003f,
					  0x0000003f, 0x00000001); break;
		case 0x00000001: SET_ABCD(0x04000122, 0x01c0003f,
					  0x0000003f, 0x00000001); break;
		case 0x00000002: SET_ABCD(0x04004143, 0x03c0003f,
					  0x00000fff, 0x00000001); break;
		default:         SET_ABCD(0x00000000, 0x00000000,
					  0x00000000, 0x00000000); break;
		}
		break;
	}
	case 0x00000005:
		SET_ABCD(0x00000040, 0x00000040, 0x00000003, 0x00000020);
		break;
	case 0x00000006:
		SET_ABCD(0x00000001, 0x00000002, 0x00000001, 0x00000000);
		break;
	case 0x00000007:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000008:
		SET_ABCD(0x00000400, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000009:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x0000000a:
	unhandled_eax_value:
		SET_ABCD(0x07280202, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000000:
		SET_ABCD(0x80000008, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000001:
		SET_ABCD(0x00000000, 0x00000000, 0x00000001, 0x20100800);
		break;
	case 0x80000002:
		SET_ABCD(0x65746e49, 0x2952286c, 0x726f4320, 0x4d542865);
		break;
	case 0x80000003:
		SET_ABCD(0x43203229, 0x20205550, 0x20202020, 0x20202020);
		break;
	case 0x80000004:
		SET_ABCD(0x30303636, 0x20402020, 0x30342e32, 0x007a4847);
		break;
	case 0x80000005:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000006:
		SET_ABCD(0x00000000, 0x00000000, 0x10008040, 0x00000000);
		break;
	case 0x80000007:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000008:
		SET_ABCD(0x00003024, 0x00000000, 0x00000000, 0x00000000);
		break;
	default:         
		goto unhandled_eax_value;
	}
#undef SET_ABCD
}

void amd64g_dirtyhelper_storeF80le(ULong addrU, ULong f64);

static struct expression_result
do_dirty_call(IRDirty *details, struct interpret_state *is)
{
	struct expression_result args[6];
	unsigned x;
	struct expression_result res = {0, 0};

	if (details->guard) {
		struct expression_result guard = eval_expression(is, details->guard);
		if (force(!guard.lo))
			return res;
	}
	for (x = 0; details->args[x]; x++) {
		tl_assert(x < 6);
		args[x] = eval_expression(is, details->args[x]);
	}
	tl_assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		res.lo = record_rdtsc();
		res.hi = res.lo >> 32;
		res.lo &= 0xffffffff;
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		res.lo = helper_load_8((const void *)args[0].lo, 0, 0);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		res.lo = helper_load_16((const void *)args[0].lo, 0, 0);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		res.lo = helper_load_32((const void *)args[0].lo, 0, 0);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		res.lo = helper_load_64((const void *)args[0].lo, 0, 0);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		ultralong_t a;
		a = helper_load_128((const void *)args[0].lo, 0, 0);
		memcpy(&res, &a, sizeof(a));
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_CPUID_sse3_and_cx16")) {
		my_amd64g_dirtyhelper_CPUID_sse3_and_cx16(is->regs);
	} else if (!strcmp(details->cee->name, "record_instr")) {
		record_instr(args[0].lo,
			     args[1].lo,
			     args[2].lo,
			     args[3].lo,
			     args[4].lo,
			     args[5].lo);
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_storeF80le") ||
		   !strcmp(details->cee->name, "amd64g_dirtyhelper_loadF80le")) {
		res.lo = ((ULong (*)(ULong, ULong, ULong,
				     ULong, ULong, ULong))
			  details->cee->addr)
			(args[0].lo, args[1].lo, args[2].lo,
			 args[3].lo, args[4].lo, args[5].lo);
	} else {
		VG_(printf)("Unknown dirty call %s\n", details->cee->name);
		VG_(printf)("%d regparms\n", details->cee->regparms);
		VG_(tool_panic)((Char *)"dead");
	}
	return res;
}

static const UChar parity_table[256] = {
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
};

static void
calculate_condition_flags_XXX(ait op,
			      ait dep1,
			      ait dep2,
			      ait ndep,
			      ait *cf,
			      ait *zf,
			      ait *sf,
			      ait *of,
			      ait *pf)
{
	*cf = *zf = *sf = *of = *pf = mkConst(0);

	switch (force(op)) {
	case AMD64G_CC_OP_COPY:
		*cf = dep1;
		*zf = dep1 >> mkConst(6);
		*sf = dep1 >> mkConst(7);
		*of = dep1 >> mkConst(11);
		*pf = dep1 >> mkConst(2);
		break;

#define DO_ACT(name, type_tag, bits)					\
		case AMD64G_CC_OP_ ## name ## type_tag:			\
			ACTIONS_ ## name (mkConst(bits));		\
		        break
#define ACTION(name)							\
		DO_ACT(name, B, 7);					\
		DO_ACT(name, W, 15);					\
		DO_ACT(name, L, 31);					\
		DO_ACT(name, Q, 63)
/* A shift of 64 bits in a 64 bit type is undefined, so we can't just
   go (1ul << 64).  However, (1ul << 63) * 2 does the right thing. */
#define MASK(bits) ((mkConst(1) << bits) * mkConst(2) - mkConst(1))
#define ACTIONS_ADD(bits)						\
		do {							\
			ait res;					\
			res = (dep1 + dep2) & MASK(bits);		\
			*cf = res < (dep1 & MASK(bits));		\
			*zf = (res == mkConst(0));			\
			*sf = (res >> bits);				\
			*of = (~(dep1 ^ dep2) &				\
			      (dep1 ^ res)) >> bits;			\
			*pf = parity_table[(UChar)res];			\
		} while (0)
#define ACTIONS_ADC(bits)	 		                        \
		do {							\
			ait oldC = ndep & AMD64G_CC_MASK_C;		\
			ait argR = dep2 ^ oldC;				\
			ait res = ((dep1 + argR) + oldC) & MASK(bits);	\
			if (oldC)					\
				*cf = res <= (dep1 & MASK(bits));	\
			else						\
				*cf = res < (dep1 & MASK(bits));	\
			*zf = res == 0;					\
			*sf = res >> bits;				\
			*of = (~(dep1 ^ argR) & (dep1 ^ res)) >> bits;	\
			*pf = parity_table[(UChar)res];			\
		} while (0)
#define ACTIONS_SUB(bits)						\
		do {							\
			ait res;					\
			res = (dep1 - dep2) & MASK(bits);		\
			sanity_check_ait(res);				\
			*cf = (dep1 & MASK(bits)) < (dep2 & MASK(bits));	\
			*zf = (res == mkConst(0));			\
			sanity_check_ait(*zf);				\
			*sf = res >> bits;				\
			*of = ( (dep1 ^ dep2) &				\
			       (dep1 ^ res) ) >> bits;			\
			*pf = parity_table[(UChar)res];			\
		} while (0)
#define ACTIONS_LOGIC(bits)						\
		do {							\
			*cf = mkConst(0);				\
			*zf = (dep1 & MASK(bits)) == mkConst(0);	\
			*sf = (dep1 & MASK(bits)) >> bits;		\
			*of = mkConst(0);				\
			*pf = parity_table[(UChar)dep1];		\
		} while (0)
#define ACTIONS_INC(bits)			                        \
		do {				                        \
			ait res = dep1 & MASK(bits);			\
			*cf = ndep & mkConst(1);			\
			*zf = (res == mkConst(0));			\
			*sf = res >> bits;				\
			*of = res == (mkConst(1) << bits);		\
			*pf = parity_table[(UChar)res];			\
		} while (0)
#define ACTIONS_DEC(bits)			                        \
		do {				                        \
			ait res = dep1 & MASK(bits);			\
			*cf = ndep & mkConst(1);			\
			*zf = (res == mkConst(0));			\
			*sf = res >> bits;				\
			*of = ((res + mkConst(1)) & MASK(bits)) == (mkConst(1) << bits); \
			*pf = parity_table[(UChar)res];			\
		} while (0)
#define ACTIONS_SHR(bits)			                        \
		do {				                        \
			*cf = dep2 & mkConst(1);			\
			*zf = (dep1 == mkConst(0));			\
			*sf = dep1 >> bits;				\
			*of = (dep1 ^ dep2) >> bits;			\
			*pf = parity_table[(UChar)dep1];		\
		} while (0)

	ACTION(ADD);
	ACTION(SUB);
	ACTION(LOGIC);
	ACTION(INC);
	ACTION(DEC);
	ACTION(SHR);
	ACTION(ADC);
#undef DO_ACT
#undef ACTION
#undef ACTIONS_ADD
#undef ACTIONS_SUB
#undef ACTIONS_LOGIC
#undef ACTIONS_INC
#undef ACTIONS_DEC
#undef ACTIONS_SHR
	default:
		VG_(printf)("Strange operation code %ld\n", force(op));
		VG_(tool_panic)((Char *)"dead");
	}

	*of &= mkConst(1);
	*sf &= mkConst(1);
	*zf &= mkConst(1);
	*cf &= mkConst(1);
}

static struct expression_result
do_ccall_calculate_condition(struct expression_result *args)
{
	struct expression_result condcode = args[0];
	struct expression_result op       = args[1];
	struct expression_result dep1     = args[2];
	struct expression_result dep2     = args[3];
	struct expression_result ndep     = args[4];
	struct expression_result res;
	ait inv;
	ait cf, zf, sf, of, pf;

	calculate_condition_flags_XXX(op.lo,
				      dep1.lo,
				      dep2.lo,
				      ndep.lo,
				      &cf,
				      &zf,
				      &sf,
				      &of,
				      &pf);

	inv = condcode.lo & mkConst(1);
	switch (force(condcode.lo & ~mkConst(1))) {
	case AMD64CondZ:
		res.lo = zf;
		break;
	case AMD64CondL:
		res.lo = sf ^ of;
		break;
	case AMD64CondLE:
		res.lo = (sf ^ of) | zf;
		break;
	case AMD64CondB:
		res.lo = cf;
		break;
	case AMD64CondBE:
		res.lo = cf | zf;
		break;
	case AMD64CondS:
		res.lo = sf;
		break;
	case AMD64CondP:
		res.lo = pf;
		break;

	default:
		VG_(printf)("Strange cond code %ld (op %ld)\n", force(condcode.lo), force(op.lo));
		VG_(tool_panic)((Char *)"dead\n");
	}

	res.lo ^= inv;

	return res;
}

static struct expression_result
do_ccall_calculate_rflags_c(struct expression_result *args)
{
	struct expression_result op   = args[0];
	struct expression_result dep1 = args[1];
	struct expression_result dep2 = args[2];
	struct expression_result ndep = args[3];
	struct expression_result res;
	ait cf, zf, sf, of, pf;

	calculate_condition_flags_XXX(op.lo,
				      dep1.lo,
				      dep2.lo,
				      ndep.lo,
				      &cf,
				      &zf,
				      &sf,
				      &of,
				      &pf);

	res.lo = cf;
	return res;
}

static struct expression_result
do_ccall_generic(IRCallee *cee,
		 struct expression_result *rargs)
{
	struct expression_result res;

	res.lo = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				     unsigned long, unsigned long, unsigned long))cee->addr)
		(force(rargs[0].lo),
		 force(rargs[1].lo),
		 force(rargs[2].lo),
		 force(rargs[3].lo),
		 force(rargs[4].lo),
		 force(rargs[5].lo));
	res.hi = mkConst(0);
	return res;
}

static struct expression_result
do_ccall(struct interpret_state *is, IRCallee *cee, IRExpr **args)
{
	struct expression_result rargs[6];
	unsigned x;

	tl_assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		tl_assert(x < 6);
		rargs[x] = eval_expression(is, args[x]);
	}
	if (!strcmp(cee->name, "amd64g_calculate_condition")) {
		return do_ccall_calculate_condition(rargs);
	} else if (!strcmp(cee->name, "amd64g_calculate_rflags_c")) {
		return do_ccall_calculate_rflags_c(rargs);
	} else {
		if (strcmp(cee->name, "amd64g_calculate_rflags_all"))
			VG_(printf)("Unknown clean call %s\n", cee->name);
		return do_ccall_generic(cee, rargs);
	}
}

/* Borrowed from gnucash */
static void mulls64(struct expression_result *dest, struct expression_result src1,
		    struct expression_result src2)
{
	int isneg = 0;
	unsigned long a = src1.lo;
	unsigned long b = src2.lo;
	unsigned long a0, a1;
	unsigned long b0, b1;
	unsigned long d, d0, d1;
	unsigned long e, e0, e1;
	unsigned long f, f0, f1;
	unsigned long g, g0, g1;
	unsigned long sum, carry, roll, pmax;
 
	if (0 > a)
	{
		isneg = !isneg;
		a = -a;
	}
 
	if (0 > b)
	{
		isneg = !isneg;
		b = -b;
	}
 
	a1 = a >> 32;
	a0 = a - (a1 << 32);
 
	b1 = b >> 32;
	b0 = b - (b1 << 32);
 
	d = a0 * b0;
	d1 = d >> 32;
	d0 = d - (d1 << 32);
 
	e = a0 * b1;
	e1 = e >> 32;
	e0 = e - (e1 << 32);
 
	f = a1 * b0;
	f1 = f >> 32;
	f0 = f - (f1 << 32);
 
	g = a1 * b1;
	g1 = g >> 32;
	g0 = g - (g1 << 32);
 
	sum = d1 + e0 + f0;
	carry = 0;
	/* Can't say 1<<32 cause cpp will goof it up; 1ULL<<32 might work */
	roll = 1 << 30;
	roll <<= 2;
 
	pmax = roll - 1;
	while (pmax < sum)
	{
		sum -= roll;
		carry ++;
	}
 
	dest->lo = d0 + (sum << 32);
	dest->hi = carry + e1 + f1 + g0 + (g1 << 32);
	if (isneg) {
		dest->lo = ~dest->lo;
		dest->hi = ~dest->hi;
		dest->lo++;
		if (dest->lo == 0)
			dest->hi++;
	}
}

static struct expression_result
eval_expression(struct interpret_state *is, IRExpr *expr)
{
	struct expression_result res;
	struct expression_result *dest = &res;
	ait v1;
	unsigned sub_word_offset;
	unsigned offset;
	IRType getType;

	res.lo = mkConst(0);
	res.hi = mkConst(0);
	
	switch (expr->tag) {
	case Iex_Get:
		offset = expr->Iex.Get.offset;
		getType = expr->Iex.Get.ty;
	do_get:
		sub_word_offset = offset & 7;
		v1 = read_reg(is->regs, offset - sub_word_offset);
		switch (getType) {
		case Ity_I64:
		case Ity_F64:
			tl_assert(!sub_word_offset);
			dest->lo = v1;
			break;
		case Ity_V128:
			tl_assert(!sub_word_offset);
			dest->lo = v1;
			dest->hi = read_reg(is->regs, offset - sub_word_offset + 8);
			break;
		case Ity_I32:
		case Ity_F32:
			tl_assert(!(sub_word_offset % 4));
			dest->lo = (v1 >> mkConst(sub_word_offset * 8)) & mkConst(0xffffffff);
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->lo = (v1 >> mkConst(sub_word_offset * 8)) & mkConst(0xffff);
			break;
		case Ity_I8:
			dest->lo = (v1 >> mkConst(sub_word_offset * 8)) & mkConst(0xff);
			break;
		default:
			ppIRExpr(expr);
			VG_(tool_panic)((Char *)"NotImplementedException");
		}
		break;

	case Iex_GetI: {
		struct expression_result idx = eval_expression(is, expr->Iex.GetI.ix);
		idx.lo += expr->Iex.GetI.bias;
		idx.lo %= expr->Iex.GetI.descr->nElems;
		idx.lo *= sizeofIRType(expr->Iex.GetI.descr->elemTy);
		idx.lo += expr->Iex.GetI.descr->base;
		offset = idx.lo;
		getType = expr->Iex.GetI.descr->elemTy;
		goto do_get;
	}

	case Iex_RdTmp:
		*dest = is->temporaries[expr->Iex.RdTmp.tmp];
		break;

	case Iex_Load: {
		dest->lo = 0;
		dest->hi = 0;
		switch (expr->Iex.Load.ty) {
		case Ity_I8:
			dest->lo = helper_load_8(
				(void *)eval_expression(is, expr->Iex.Load.addr).lo,
				0,
				0);
			break;
		case Ity_I16:
			dest->lo = helper_load_16(
				(void *)eval_expression(is, expr->Iex.Load.addr).lo,
				0,
				0);
			break;
		case Ity_I32:
		case Ity_F32:
			dest->lo = helper_load_32(
				(void *)eval_expression(is, expr->Iex.Load.addr).lo,
				0,
				0);
			break;
		case Ity_I64:
		case Ity_F64:
			dest->lo = helper_load_64(
				(void *)eval_expression(is, expr->Iex.Load.addr).lo,
				0,
				0);
			break;
		case Ity_I128:
		case Ity_V128: {
			ultralong_t a;
			a = helper_load_128(
				(void *)eval_expression(is, expr->Iex.Load.addr).lo,
				0,
				0);
			memcpy(dest, &a, sizeof(a));
			break;
		}
		default:
			VG_(tool_panic)((Char *)"transform_expr failed to remove all load expressions\n");
		}
		break;
	}

	case Iex_Const: {
		IRConst *cnst = expr->Iex.Const.con;
		switch (cnst->tag) {
		case Ico_U1:
			dest->lo = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->lo = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->lo = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->lo = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo = cnst->Ico.U64;
			break;
		case Ico_V128: {
			unsigned long r = cnst->Ico.V128;
			r = r | (r << 16) | (r << 32) | (r << 48);
			dest->lo = r;
			dest->hi = dest->lo;
			break;
		}
		default:
			ppIRExpr(expr);
			VG_(tool_panic)((Char *)"NotImplementedException()");
		}
		break;
	}

	case Iex_Binop: {
		struct expression_result arg1 = eval_expression(is, expr->Iex.Binop.arg1);
		struct expression_result arg2 = eval_expression(is, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub8:
		case Iop_Sub16:
		case Iop_Sub32:
		case Iop_Sub64:
			dest->lo = arg1.lo - arg2.lo;
			break;
		case Iop_Add8:
		case Iop_Add16:
		case Iop_Add32:
		case Iop_Add64:
			dest->lo = arg1.lo + arg2.lo;
			break;
		case Iop_Add64x2:
			dest->lo = arg1.lo + arg2.lo;
			dest->hi = arg1.hi + arg2.hi;
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo = arg1.lo & arg2.lo;
			break;
		case Iop_Or8:
		case Iop_Or16:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo = arg1.lo | arg2.lo;
			break;
		case Iop_Shl16:
		case Iop_Shl32:
		case Iop_Shl64:
			dest->lo = arg1.lo << arg2.lo;
			break;
		case Iop_Sar64:
			dest->lo = (long)arg1.lo >> arg2.lo;
			break;
		case Iop_Shr16:
		case Iop_Shr32:
		case Iop_Shr64:
			dest->lo = arg1.lo >> arg2.lo;
			break;
		case Iop_XorV128:
		case Iop_Xor64:
		case Iop_Xor32:
		case Iop_Xor16:
		case Iop_Xor8:
			dest->lo = arg1.lo ^ arg2.lo;
			dest->hi = arg1.hi ^ arg2.hi;
			break;
		case Iop_CmpNE8:
			dest->lo = arg1.lo != arg2.lo;
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo = arg1.lo == arg2.lo;
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo = arg1.lo != arg2.lo;
			break;
		case Iop_CmpLE64U:
			dest->lo = arg1.lo <= arg2.lo;
			break;
		case Iop_CmpLE64S:
			dest->lo = (long)arg1.lo <= (long)arg2.lo;
			break;
		case Iop_CmpLT64S:
			dest->lo = (long)arg1.lo < (long)arg2.lo;
			break;
		case Iop_CmpLT64U:
			dest->lo = arg1.lo < arg2.lo;
			break;
		case Iop_Mul64:
		case Iop_Mul32:
			dest->lo = arg1.lo * arg2.lo;
			break;

		case Iop_MullU32:
			dest->lo = arg1.lo * arg2.lo;
			break;
		case Iop_MullS32:
			dest->lo =
				(long)(int)force(arg1.lo) * (long)(int)force(arg2.lo);
			break;

		case Iop_MullS64:
			mulls64(dest, arg1, arg2);
			break;

		case Iop_MullU64: {
			ait a1, a2, b1, b2;
			dest->lo = arg1.lo * arg2.lo;
			a1 = arg1.lo & mkConst(0xffffffff);
			a2 = arg1.lo >> mkConst(32);
			b1 = arg2.lo & mkConst(0xffffffff);
			b2 = arg2.lo >> mkConst(32);
			dest->hi = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> mkConst(32))) >> mkConst(32));
			break;
		}
		case Iop_32HLto64:
			dest->lo = (arg1.lo << mkConst(32)) | arg2.lo;
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_DivModU64to32:
			dest->lo = (arg1.lo / arg2.lo) |
				((arg1.lo % arg2.lo) << mkConst(32));
			break;

		case Iop_DivModS64to32: {
			long a1 = force(arg1.lo);
			long a2 = force(arg2.lo);
			dest->lo =
				((a1 / a2) & 0xffffffff) | ((a1 % a2) << 32);
			break;
		}

		case Iop_DivModU128to64: {
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			unsigned long dlo, dhi;
			asm ("div %4\n"
			     : "=a" (dlo), "=d" (dhi)
			     : "0" (force(arg1.lo)), "1" (force(arg1.hi)), "r" (force(arg2.lo)));
			dest->lo = dlo;
			dest->hi = dhi;
			break;
		}

		case Iop_DivModS128to64: {
			unsigned long dlo;
			unsigned long dhi;
			asm ("idiv %4\n"
			     : "=a" (dlo), "=d" (dhi)
			     : "0" (force(arg1.lo)), "1" (force(arg1.hi)), "r" (force(arg2.lo)));
			dest->lo = dlo;
			dest->hi = dhi;
			break;
		}

		case Iop_Add32x4:
			dest->lo = ((arg1.lo + arg2.lo) & mkConst(0xffffffff)) +
				((arg1.lo & ~0xfffffffful) + (arg2.lo & ~0xfffffffful));
			dest->hi = ((arg1.hi + arg2.hi) & mkConst(0xffffffff)) +
				((arg1.hi & ~0xfffffffful) + (arg2.hi & ~0xfffffffful));
			break;

		case Iop_InterleaveLO64x2:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_InterleaveHI64x2:
			dest->lo = arg2.hi;
			dest->hi = arg1.hi;
			break;

		case Iop_InterleaveLO32x4:
			dest->lo = (arg2.lo & mkConst(0xffffffff)) | (arg1.lo << mkConst(32));
			dest->hi = (arg2.lo >> mkConst(32)) | (arg1.lo & 0xffffffff00000000ul);
			break;

		case Iop_InterleaveHI32x4:
			dest->lo = (arg2.hi & mkConst(0xffffffff)) | (arg1.hi << mkConst(32));
			dest->hi = (arg2.hi >> mkConst(32)) | (arg1.hi & 0xffffffff00000000ul);
			break;

		case Iop_ShrN64x2:
			dest->lo = arg1.lo >> arg2.lo;
			dest->hi = arg1.hi >> arg2.lo;
			break;

		case Iop_ShlN64x2:
			dest->lo = arg1.lo << arg2.lo;
			dest->hi = arg1.hi << arg2.lo;
			break;

		case Iop_CmpGT32Sx4: {
			unsigned long a1l = force(arg1.lo);
			unsigned long a2l = force(arg2.lo);
			unsigned long a1h = force(arg1.hi);
			unsigned long a2h = force(arg2.hi);
			if ( (int)a1l > (int)a2l )
				dest->lo |= mkConst(0xffffffff);
			if ( (int)(a1l >> 32) > (int)(a2l >> 32) )
				dest->lo |= mkConst(0xffffffff00000000);
			if ( (int)a1h > (int)a2h )
				dest->hi |= mkConst(0xffffffff);
			if ( (int)(a1h >> 32) > (int)(a2h >> 32) )
				dest->hi |= mkConst(0xffffffff00000000);
			break;
		}

		case Iop_CmpF64: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = force(arg1.lo);
			r2.l = force(arg2.lo);
			double a1 = r1.d;
			double a2 = r2.d;
			unsigned long r;
			if (a1 < a2)
				r = 1;
			else if (a1 == a2)
				r = 0x40;
			else if (a1 > a2)
				r = 0;
			else
				r = 0x45;
			dest->lo = r;
			break;
		}

		case Iop_Mul64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d * r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Div64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d / r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Add64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d + r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Min64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			if (r1.d < r2.d)
				res.d = r1.d;
			else
				res.d = r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Max64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			if (r1.d > r2.d)
				res.d = r1.d;
			else
				res.d = r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Sub64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d - r2.d;
			dest->lo = res.l;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_CmpLT64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			dest->lo = r1.d < r2.d;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_CmpEQ64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			dest->lo = r1.d == r2.d;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_CmpLE64F0x2: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			dest->lo = r1.d <= r2.d;
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Div32F0x4: {
			union {
				float d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d / r2.d;
			dest->lo = (res.l & 0xffffffff) | (arg1.lo & 0xffffffff00000000ul);
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Mul32F0x4: {
			union {
				float d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d * r2.d;
			dest->lo = (res.l & 0xffffffff) | (arg1.lo & 0xffffffff00000000ul);
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Add32F0x4: {
			union {
				float d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d + r2.d;
			dest->lo = (res.l & 0xffffffff) | (arg1.lo & 0xffffffff00000000ul);
			dest->hi = arg1.hi;
			break;
		}

		case Iop_Sub32F0x4: {
			union {
				float d;
				unsigned long l;
			} r1, r2, res;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			res.d = r1.d - r2.d;
			dest->lo = (res.l & 0xffffffff) | (arg1.lo & 0xffffffff00000000ul);
			dest->hi = arg1.hi;
			break;
		}

		case Iop_AndV128:
			dest->lo = arg1.lo & arg2.lo;
			dest->hi = arg1.hi & arg2.hi;
			break;

		case Iop_OrV128:
			dest->lo = arg1.lo | arg2.lo;
			dest->hi = arg1.hi | arg2.hi;
			break;

		case Iop_I64StoF64: {
			long t = arg2.lo;
			union {
				double res_d;
				unsigned long res_l;
			} u;
			u.res_d = t;
			dest->lo = u.res_l;
			break;
		}

		case Iop_F64toI32S: {
			union {
				double res_d;
				unsigned long res_l;
			} u;
			u.res_l = arg2.lo;
			dest->lo = (unsigned long)(int)u.res_d & 0xffffffff;
			break;
		}

		case Iop_F64toI64S: {
			union {
				double res_d;
				unsigned long res_l;
			} u;
			u.res_l = arg2.lo;
			dest->lo = (long)u.res_d;
			break;
		}

		case Iop_F64toF32: {
			union {
				double d;
				unsigned long l;
			} in;
			union {
				float f;
				unsigned long l;
			} out;
			in.l = arg2.lo;
			out.f = in.d;
			dest->lo = out.l;
			break;
		}

		case Iop_SetV128lo64:
			dest->lo = arg2.lo;
			dest->hi = arg1.hi;
			break;

		case Iop_SinF64: {
			union {
				double f;
				unsigned long l;
			} in, out;
			in.l = arg2.lo;
			asm ("fsin\n"
			     : "=t" (out.f)
			     : "0" (in.f));
			dest->lo = out.l;
			break;
		}

		case Iop_CosF64: {
			union {
				double f;
				unsigned long l;
			} in, out;
			in.l = arg2.lo;
			asm ("fcos\n"
			     : "=t" (out.f)
			     : "0" (in.f));
			dest->lo = out.l;
			break;
		}

		default:
			ppIRExpr(expr);
			VG_(printf)("Not implemented; guessing.\n");
			if (arg1.lo)
				*dest = arg1;
			else
				*dest = arg2;
			break;
		}

		IRType t, ign1, ign2, ign3, ign4;
		typeOfPrimop(expr->Iex.Binop.op, &t, &ign1, &ign2, &ign3, &ign4);
		switch (t) {
		case Ity_I1:
			dest->lo &= mkConst(1);
			break;
		case Ity_I8:
			dest->lo &= mkConst(0xff);
			break;
		case Ity_I16:
			dest->lo &= mkConst(0xffff);
			break;
		case Ity_I32:
			dest->lo &= mkConst(0xffffffff);
			break;
		case Ity_I64:
			break;

		case Ity_F32:
		case Ity_F64:
			break;

		case Ity_I128:
		case Ity_V128:
			break;
		default:
			ppIRType(t);
			VG_(tool_panic)((Char *)"NotImplementedException()");
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg = eval_expression(is, expr->Iex.Unop.arg);
		*dest = arg;
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo = arg.lo >> mkConst(32);
			break;
		case Iop_64to32:
			dest->lo = arg.lo & mkConst(0xffffffff);
			break;
		case Iop_64to16:
		case Iop_32to16:
			dest->lo = arg.lo & mkConst(0xffff);
			break;
		case Iop_64to8:
		case Iop_32to8:
		case Iop_16to8:
			dest->lo = arg.lo & mkConst(0xff);
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo = arg.lo;
			break;
		case Iop_64UtoV128:
		case Iop_32UtoV128:
			dest->lo = arg.lo;
			break;
		case Iop_64to1:
			dest->lo = arg.lo & mkConst(1);
			break;
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_16Uto32:
		case Iop_1Uto64:
		case Iop_1Uto8:
		case Iop_8Uto64:
		case Iop_8Uto32:
		case Iop_8Uto16:
			*dest = arg;
			break;
		case Iop_8Sto32:
			dest->lo = ((long)(arg.lo << mkConst(56)) >> mkConst(56)) & mkConst(0xffffffff);
			break;
		case Iop_8Sto16:
			dest->lo = ((long)(arg.lo << mkConst(56)) >> mkConst(56)) & mkConst(0xffff);
			break;
		case Iop_8Sto64:
			dest->lo = (long)(arg.lo << mkConst(56)) >> mkConst(56);
			break;
		case Iop_16Sto32:
			dest->lo = ((long)(arg.lo << mkConst(48)) >> mkConst(48)) & mkConst(0xffffffff);
			break;
		case Iop_16Sto64:
			dest->lo = ((long)(arg.lo << mkConst(48)) >> mkConst(48));
			break;
		case Iop_32Sto64:
			dest->lo = (long)(arg.lo << mkConst(32)) >> mkConst(32);
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo = arg.hi;
			break;

		case Iop_Not1:
			dest->lo = !arg.lo;
			break;

		case Iop_Not32:
			dest->lo = ~arg.lo & mkConst(0xffffffff);
			break;

		case Iop_Not64:
			dest->lo = ~arg.lo;
			break;

		case Iop_NotV128:
			dest->lo = ~arg.lo;
			dest->hi = ~arg.hi;
			break;

		case Iop_Clz64: {
			unsigned long v = force(arg.lo);
			unsigned res = 0;
			while (!(v & (1ul << (63 - res))) &&
			       res < 63)
				res++;
			dest->lo = res;
			break;
		}

		case Iop_Ctz64: {
			unsigned long v = force(arg.lo);
			unsigned res = 0;
			while (!(v & (1ul << res)) &&
			       res < 63)
				res++;
			dest->lo = res;
			break;
		}

		case Iop_I32StoF64: {
			int t = arg.lo;
			union {
				double res_d;
				unsigned long res_l;
			} u;
			u.res_d = t;
			dest->lo = u.res_l;
			break;
		}

		case Iop_F32toF64: {
			union {
				float f;
				unsigned long l;
			} in;
			union {
				double f;
				unsigned long l;
			} out;
			in.l = arg.lo;
			out.f = in.f;
			dest->lo = out.l;
			break;
		}

		case Iop_ReinterpF64asI64:
		case Iop_ReinterpF32asI32:
		case Iop_ReinterpI64asF64:
		case Iop_ReinterpI32asF32:
			*dest = arg;
			break;

		case Iop_Sqrt64F0x2: {
			union {
				double f;
				unsigned long l;
			} in, out;
			in.l = arg.lo;
			asm ("fsqrt\n"
			     : "=t" (out.f)
			     : "0" (in.f));
			dest->lo = out.l;
			break;
		}

		default:
			ppIRExpr(expr);
			VG_(printf)("Can't handle this unop; guessing.\n");
			*dest = arg;
		}
		break;
	}

	case Iex_Triop: {
		struct expression_result arg1 = eval_expression(is, expr->Iex.Triop.arg1);
		struct expression_result arg2 = eval_expression(is, expr->Iex.Triop.arg2);
		struct expression_result arg3 = eval_expression(is, expr->Iex.Triop.arg3);
		switch (expr->Iex.Triop.op) {
		case Iop_PRemF64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, res;
			a1.l = arg2.lo;
			a2.l = arg3.lo;
			asm ("fprem\n"
			     : "=t" (res.d)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo = res.l;
			break;
		}
		case Iop_PRemC3210F64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, clobber;
			unsigned short res;
			a1.l = arg2.lo;
			a2.l = arg3.lo;
			asm ("fprem\nfstsw %%ax\n"
			     : "=t" (clobber.d), "=a" (res)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo = ((res >> 8) & 7) | ((res & 0x400) >> 11);
			break;
		}
		default:
			ppIRExpr(expr);
			VG_(printf)("Can't handle triop expression!\n");
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result cond = eval_expression(is, expr->Iex.Mux0X.cond);
		struct expression_result res0 = eval_expression(is, expr->Iex.Mux0X.expr0);
		struct expression_result resX = eval_expression(is, expr->Iex.Mux0X.exprX);
		if (force(cond.lo == mkConst(0))) {
			*dest = res0;
		} else {
			*dest = resX;
		}
		break;
	}

	case Iex_CCall: {
		res = do_ccall(is, expr->Iex.CCall.cee, expr->Iex.CCall.args);
		break;
	}

	default:
		ppIRExpr(expr);
		VG_(printf)("Bad expression tag %x\n", expr->tag);
	}

	return res;
}

IRSB *instrument_func(void *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

struct cache_entry {
	unsigned long addr;
	IRSB *irsb;
};

struct cache_entry l1_cache[64];
struct cache_entry l2_cache[8192];

#define L2_DELETE ((IRSB *)1)

static unsigned long hash_rip(unsigned long rip, unsigned long bits)
{
	unsigned long acc = 0;
	unsigned long mask = (1ul << bits) - 1;

	while (rip & ~mask) {
		acc = (acc ^ rip) & mask;
		rip >>= bits;
	}
	return acc;
}

static void l2_insert(unsigned long rip, IRSB *irsb)
{
	unsigned probe;
	unsigned bit;

	probe = hash_rip(rip, 13);
	for (bit = 13; bit > 0; bit--) {
		if (l2_cache[probe].irsb == 0 ||
		    l2_cache[probe].irsb == L2_DELETE) {
			l2_cache[probe].addr = rip;
			l2_cache[probe].irsb = irsb;
			return;
		}
		probe ^= 1 << (bit - 1);
	}
	/* No more room.  Drop the irsb on the floor; the GC should
	   pick it up later.  */
}

static int cache_lookup(unsigned long rip, IRSB ***slot)
{
	struct cache_entry *ce1;
	struct cache_entry evicted;
	unsigned probe;
	unsigned bit;

	/* Check L1 first */
	ce1 = &l1_cache[hash_rip(rip, 6)];
	*slot = &ce1->irsb;
	if (ce1->addr == rip)
		return 1;

	/* Now check l2 */
	probe = hash_rip(rip, 13);
	if (l2_cache[probe].addr == rip) {
	found_l2:
		evicted = *ce1;
		*ce1 = l2_cache[probe];
		l2_cache[probe].addr = 0;
		l2_cache[probe].irsb = L2_DELETE;
		l2_insert(evicted.addr, evicted.irsb);
		return 1;
	}

	for (bit = 13; bit > 0; bit--) {
		probe ^= 1 << (bit - 1);
		if (l2_cache[probe].addr == rip)
			goto found_l2;
		if (!l2_cache[probe].irsb)
			break;
	}

	/* Give up */
	if (ce1->addr != 0) {
		evicted = *ce1;
		l2_insert(evicted.addr, evicted.irsb);
	}
	ce1->addr = rip;
	ce1->irsb = NULL;
	return 0;
}

void zap_cache()
{
	VG_(memset)(l1_cache, 0, sizeof(l1_cache));
	VG_(memset)(l2_cache, 0, sizeof(l2_cache));
}

static void translateNextBlock(struct interpret_state *is)
{
	IRSB **cache_slot;
	unsigned input, output;

	VG_(init_vex)();

	vexSetAllocModeTEMP_and_clear();

	is->currentIRSBOffset = 0;
	if (cache_lookup(is->regs->guest_RIP, &cache_slot)) {
		is->currentIRSB = *cache_slot;
		return;
	}

	VexArchInfo archinfo_guest;
	VexAbiInfo abiinfo_both;
	VexGuestExtents vge;
	LibVEX_default_VexArchInfo(&archinfo_guest);
	archinfo_guest.hwcaps =
		VEX_HWCAPS_AMD64_SSE3|
		VEX_HWCAPS_AMD64_CX16;
	LibVEX_default_VexAbiInfo(&abiinfo_both);
	abiinfo_both.guest_stack_redzone_size = 128;
	abiinfo_both.guest_amd64_assume_fs_is_zero = 1;
	IRSB *irsb = bb_to_IR(&vge,
			      NULL, /* Context for chase_into_ok */
			      disInstr_AMD64,
			      (UChar *)is->regs->guest_RIP,
			      (Addr64)is->regs->guest_RIP,
			      chase_into_ok,
			      False, /* host bigendian */
			      VexArchAMD64,
			      &archinfo_guest,
			      &abiinfo_both,
			      Ity_I64, /* guest word type */
			      False, /* do_self_check */
			      NULL, /* preamble */
			      0, /* self check start */
			      0); /* self check len */
	if (!irsb)
		VG_(tool_panic)((Char *)"InstructionDecodeFailedException()");

	tl_assert(irsb->tyenv->types_used <= LibVEX_N_SPILL_BYTES / sizeof(struct expression_result));

	output = 0;
	for (input = 0; input < irsb->stmts_used; input++) {
		if (irsb->stmts[input]->tag != Ist_IMark) {
			irsb->stmts[output] = irsb->stmts[input];
			output++;
		}
	}
	irsb->stmts_used = output;
	*cache_slot = is->currentIRSB = irsb;
}

static unsigned
runToEvent(struct interpret_state *is)
{
	unsigned offset;
	struct expression_result put_data;
	IRType put_type;
	static unsigned long nr_ops;

	while (1) {
		if (!is->currentIRSB) {
			if (VG_(dispatch_ctr) == 1)
				return VG_TRC_INNER_COUNTERZERO;
			VG_(dispatch_ctr)--;
			translateNextBlock(is);
			tl_assert(is->currentIRSB);
		}
		while (is->currentIRSBOffset < is->currentIRSB->stmts_used) {
			IRStmt *stmt = is->currentIRSB->stmts[is->currentIRSBOffset];
			is->currentIRSBOffset++;

			nr_ops++;
			if (nr_ops % 10000000 == 0)
				VG_(printf)("Done %ld ops\n", nr_ops);

			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
#if 0
				record_instr(stmt->Ist.IMark.addr,
					     read_reg(is->regs, FOOTSTEP_REG_0_OFFSET),
					     read_reg(is->regs, FOOTSTEP_REG_1_OFFSET),
					     read_reg(is->regs, FOOTSTEP_REG_2_OFFSET),
					     read_reg(is->regs, FOOTSTEP_REG_3_OFFSET),
					     read_reg(is->regs, FOOTSTEP_REG_4_OFFSET));
#endif
				break;
			case Ist_AbiHint:
				break;
			case Ist_MBE:
				break;
			case Ist_WrTmp:
				is->temporaries[stmt->Ist.WrTmp.tmp] =
					eval_expression(is,stmt->Ist.WrTmp.data);
				DBG("temp %d -> %016lx%016lx\n",
				    stmt->Ist.WrTmp.tmp,
				    is->temporaries[stmt->Ist.WrTmp.tmp].hi,
				    is->temporaries[stmt->Ist.WrTmp.tmp].lo);
				break;

			case Ist_Store: {
				tl_assert(stmt->Ist.Store.end == Iend_LE);
				struct expression_result data =
					eval_expression(is, stmt->Ist.Store.data);
				struct expression_result addr =
					eval_expression(is, stmt->Ist.Store.addr);
				unsigned size = sizeofIRType(typeOfIRExpr(is->currentIRSB->tyenv,
									  stmt->Ist.Store.data));
				DBG("store %016lx%016lx:%d @ %016lx%016lx\n",
				    addr.hi,
				    addr.lo,
				    size,
				    data.hi,
				    data.lo);
				switch (size) {
				case 1:
					helper_store_8((void *)addr.lo,
						       data.lo,
						       0,
						       0);
					break;
				case 2:
					helper_store_16((void *)addr.lo,
						       data.lo,
						       0,
						       0);
					break;
				case 4:
					helper_store_32((void *)addr.lo,
						       data.lo,
						       0,
						       0);
					break;
				case 8:
					helper_store_64((void *)addr.lo,
							data.lo,
							0,
							0);
					break;
				case 16: {
					ultralong_t a;
					memcpy(&a, &data, sizeof(data));
					helper_store_128((void *)addr.lo,
							 a,
							 0,
							 0);
					break;
				}
				default:
					VG_(printf)("Odd sized (%d) store\n", size);
					VG_(tool_panic)((Char *)"dead");
				}
				break;
			}

			case Ist_CAS: {
				tl_assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
				tl_assert(stmt->Ist.CAS.details->expdHi == NULL);
				tl_assert(stmt->Ist.CAS.details->dataHi == NULL);
				tl_assert(stmt->Ist.CAS.details->end == Iend_LE);
				struct expression_result data =
					eval_expression(is, stmt->Ist.CAS.details->dataLo);
				struct expression_result addr =
					eval_expression(is, stmt->Ist.CAS.details->addr);
				struct expression_result expected =
					eval_expression(is, stmt->Ist.CAS.details->expdLo);
				unsigned size = sizeofIRType(typeOfIRExpr(is->currentIRSB->tyenv,
									  stmt->Ist.CAS.details->dataLo));
				DBG("CAS %016lx%016lx:%d:%016lx%016lx -> %016lx%016lx\n",
				    addr.hi,
				    addr.lo,
				    size,
				    expected.hi,
				    expected.lo,
				    data.hi,
				    data.lo);
				switch (size) {
				case 4:
					is->temporaries[stmt->Ist.CAS.details->oldLo].lo =
						helper_cas_32((void *)addr.lo,
							      expected.lo,
							      data.lo,
							      0,
							      0);
					break;
				case 8:
					is->temporaries[stmt->Ist.CAS.details->oldLo].lo =
						helper_cas_64((void *)addr.lo,
							      expected.lo,
							      data.lo,
							      0,
							      0);
					break;
				default:
					VG_(printf)("unexpected CAS size %d\n", size);
					VG_(tool_panic)((Char *)"dead");
				}
				break;
			}

			case Ist_Put: {
				ait dest;
				unsigned byte_offset;
				offset = stmt->Ist.Put.offset;
				put_data = eval_expression(is, stmt->Ist.Put.data);
				put_type = typeOfIRExpr(is->currentIRSB->tyenv, stmt->Ist.Put.data);

				do_put:
				byte_offset = offset & 7;
				dest = read_reg(is->regs, offset - byte_offset);
				DBG("put %d -> %016lx%016lx\n",
				    offset, put_data.hi, put_data.lo);
				switch (put_type) {
				case Ity_I8:
					dest &= ~(0xFF << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I16:
					tl_assert(!(byte_offset % 2));
					dest &= ~(0xFFFFul << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I32:
				case Ity_F32:
					tl_assert(!(byte_offset % 4));
					dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I64:
				case Ity_F64:
					tl_assert(byte_offset == 0);
					dest = put_data.lo;
					break;

				case Ity_I128:
				case Ity_V128:
					tl_assert(byte_offset == 0);
					dest = put_data.lo;
					write_reg(is->regs,
						  offset + 8,
						  put_data.hi);
					break;
				default:
					ppIRStmt(stmt);
					VG_(tool_panic)((Char *)"NotImplementedException()");
				}

				write_reg(is->regs, offset - byte_offset, dest);
				break;
			}

			case Ist_Dirty: {
				struct expression_result r = do_dirty_call(stmt->Ist.Dirty.details, is);
				if (stmt->Ist.Dirty.details->tmp != IRTemp_INVALID)
					is->temporaries[stmt->Ist.Dirty.details->tmp] = r;
				break;
			}

			case Ist_Exit: {
				if (stmt->Ist.Exit.guard) {
					struct expression_result guard =
						eval_expression(is, stmt->Ist.Exit.guard);
					if (force(!guard.lo))
						break;
				}
				if (stmt->Ist.Exit.jk != Ijk_Boring) {
					tl_assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
					VG_(printf)("EMULATION WARNING %x\n",
						    is->regs->guest_EMWARN);
				}
				tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
				sanity_check_ait(currentControlCondition);
				is->regs->guest_RIP = stmt->Ist.Exit.dst->Ico.U64;
				goto finished_block;
			}

			case Ist_PutI: {
				struct expression_result idx = eval_expression(is, stmt->Ist.PutI.ix);

				/* Crazy bloody encoding scheme */
				idx.lo += stmt->Ist.PutI.bias;
				idx.lo %= stmt->Ist.PutI.descr->nElems;
				idx.lo *= sizeofIRType(stmt->Ist.PutI.descr->elemTy);
				idx.lo += stmt->Ist.PutI.descr->base;

				offset = idx.lo;
				put_data = eval_expression(is, stmt->Ist.PutI.data);
				put_type = stmt->Ist.PutI.descr->elemTy;
				goto do_put;
			}

			default:
				VG_(printf)("Don't know how to interpret statement ");
				ppIRStmt(stmt);
				VG_(tool_panic)((Char *)"NotImplementedException()");
			}
		}

		tl_assert(is->currentIRSB->jumpkind == Ijk_Boring ||
			  is->currentIRSB->jumpkind == Ijk_Call ||
			  is->currentIRSB->jumpkind == Ijk_Ret ||
			  is->currentIRSB->jumpkind == Ijk_Sys_syscall ||
			  is->currentIRSB->jumpkind == Ijk_Yield);

		{
			struct expression_result next_addr =
				eval_expression(is, is->currentIRSB->next);
			sanity_check_ait(next_addr.lo);
			is->regs->guest_RIP = next_addr.lo;
		}

		if (is->currentIRSB->jumpkind == Ijk_Yield) {
			is->currentIRSB = NULL;
			return VEX_TRC_JMP_YIELD;
		}

		if (is->currentIRSB->jumpkind == Ijk_Sys_syscall) {
			is->currentIRSB = NULL;
			return VEX_TRC_JMP_SYS_SYSCALL;
		}

finished_block:
		is->currentIRSB = NULL;
	}
}

unsigned
VG_(run_innerloop)(ThreadArchState *state, UWord do_profiling)
{
	struct interpret_state is;

	is.regs = &state->vex;
	is.temporaries = (void *)state->vex_spill;
	is.currentIRSB = NULL;
	is.currentIRSBOffset = 0;
	return runToEvent(&is);
}
