#include <asm/unistd.h>
#include <setjmp.h>
#include <stddef.h>

#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcsignal.h"
#include "pub_tool_signals.h"
#include "pub_tool_machine.h"
#include "pub_tool_options.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "libvex_trc_values.h"
#include "valgrind.h"

#include "ppres.h"
#include "ppres_client.h"
#include "coroutines.h"
#include "replay.h"
#include "replay2.h"

#include "../coregrind/pub_core_basics.h"
#include "../coregrind/pub_core_machine.h"
#include "../coregrind/pub_core_threadstate.h"
#include "../coregrind/pub_core_dispatch_asm.h"
#include "../VEX/priv/main_util.h"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"
#include "../VEX/priv/ir_opt.h"

extern Bool VG_(in_generated_code);
extern ThreadId VG_(running_tid);
extern Bool VG_(tool_handles_synchronisation);
extern ULong (*tool_provided_rdtsc)(void);
extern void (*VG_(tool_provided_thread_starting))(void);
extern Long (*tool_provided_clone_syscall)(Word (*fn)(void *),
					   void *stack,
					   Long flags,
					   void *arg,
					   Long *child_tid,
					   Long *parent_tid,
					   vki_modify_ldt_t *);
extern UInt (*VG_(interpret))(VexGuestArchState *state);
extern void VG_(client_syscall)(ThreadId tid, UInt trc);
extern SysRes VG_(am_mmap_anon_fixed_client)( Addr start, SizeT length, UInt prot );
extern void vexSetAllocModeTEMP_and_clear ( void );
extern void VG_(init_vex)(void);

/* ASSUME is like assert, in that it terminates if the argument is
   anything other than true, but it's supposed to be a hint that we're
   failing because something isn't implemented rather than because of
   a strict bug. */
#define ASSUME tl_assert

struct client_event_record {
	enum { EVENT_nothing = 0xf001,
	       EVENT_footstep,
	       EVENT_syscall,
	       EVENT_rdtsc,
	       EVENT_load,
	       EVENT_store,
	       EVENT_client_request,
	       EVENT_resched_candidate } type;
	unsigned nr_args;

	/* Careful: this is on the stack of the thread which generated
	   the event, so it becomes invalid as soon as that thread
	   gets scheduled. */
	const unsigned long *args;
};

struct abstract_interpret_value {
	unsigned long v1;
	unsigned long v2;
	struct expression *origin;
	struct expression *origin2;
};

struct interpret_state {
	struct abstract_interpret_value *temporaries;
	/* Update commit_is_to_vex_state, initialise_is_for_vex_state,
	   and get_aiv_for_offset when changing these. */
	struct abstract_interpret_value rax;
	struct abstract_interpret_value rcx;
	struct abstract_interpret_value rdx;
	struct abstract_interpret_value rbx;
	struct abstract_interpret_value rsp;
	struct abstract_interpret_value rbp;
	struct abstract_interpret_value rsi;
	struct abstract_interpret_value rdi;
	struct abstract_interpret_value r8;
	struct abstract_interpret_value r9;
	struct abstract_interpret_value r10;
	struct abstract_interpret_value r11;
	struct abstract_interpret_value r12;
	struct abstract_interpret_value r13;
	struct abstract_interpret_value r14;
	struct abstract_interpret_value r15;
	struct abstract_interpret_value rip;

	struct abstract_interpret_value cc_op;
	struct abstract_interpret_value cc_dep1;
	struct abstract_interpret_value cc_dep2;
	struct abstract_interpret_value cc_ndep;

	struct abstract_interpret_value d_flag;
	struct abstract_interpret_value fs_zero;

	struct abstract_interpret_value xmm0;
	struct abstract_interpret_value xmm1;
};

struct replay_thread {
	struct replay_thread *next;
	struct coroutine coroutine;
	ThreadId id;

	/* Hack: when we come back after satisfying a rdtsc, this is
	 * what we return. */
	ULong rdtsc_result;

	unsigned last_record_nr;
	Bool dead;
	Bool in_monitor;

	struct interpret_state interpret_state;
};

struct control_command {
	unsigned cmd;
	union {
		struct {
			long nr;
		} run;
		struct {
			long nr;
		} trace;
		struct {
			long nr;
		} control_trace;
		struct {
			long thread;
			long nr;
		} runm;
		struct {
			long thread;
		} trace_thread;
		struct {
			long address;
		} trace_mem;
	} u;
};

struct expression {
	unsigned type;
	union {
		unsigned reg;
		unsigned long cnst;
		struct {
			const void *ptr;
			unsigned size;
		} mem;
		struct {
			struct expression *arg1;
			struct expression *arg2;
		} binop;
		struct {
			struct expression *e;
		} unop;
	} u;
};

struct failure_reason {
	unsigned reason;
	struct expression *arg1;
	struct expression *arg2;
};

struct interpret_mem_lookaside {
	struct interpret_mem_lookaside *next;
	Addr ptr;
	unsigned size;
	struct abstract_interpret_value aiv;
};

static Bool
use_footsteps;

static Bool
use_memory;

static struct client_event_record *
client_event;

static struct coroutine
replay_machine;

static struct replay_thread *
head_thread;

static struct replay_thread *
current_thread;

static int
control_process_socket;

static unsigned
record_nr;

static unsigned
access_nr;

static Bool
trace_mode;

static Addr
trace_address;

static struct interpret_mem_lookaside *
head_interpret_mem_lookaside;

static void
my_mprotect(void *base, size_t len, int prot)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_mprotect), "D" (base),
	       "S" (len), "d" (prot));
}

long
my__exit(int code)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_exit), "D" (code));
	return res;
}

long
my_fork(void)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_fork));
	return res;
}

/* Safe against partial writes, but kills you if it hits any other
   errors. */
void
safeish_write(int fd, const void *buffer, size_t buffer_size)
{
	unsigned x;
	Int this_time;

	for (x = 0; x < buffer_size; x++) {
		this_time = VG_(write)(fd, buffer + x, buffer_size - x);
		if (this_time <= 0)
			VG_(tool_panic)((Char *)"writing");
		x += this_time;
	}
}

/* Likewise for read. */
void
safeish_read(int fd, void *buffer, size_t buffer_size)
{
	unsigned x;
	Int this_time;

	for (x = 0; x < buffer_size; x++) {
		this_time = VG_(read)(fd, buffer + x, buffer_size - x);
		if (this_time <= 0)
			VG_(tool_panic)((Char *)"reading");
		x += this_time;
	}
}

int
socketpair(int domain, int type, int protocol, int *fds)
{
	long res;
	register int *_fds asm ("r10") = fds;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_socketpair), "D" (domain), "S" (type),
	       "d" (protocol), "r" (_fds));
	return res;
}

size_t
recvmsg(int sockfd, struct msghdr *msg, int flags)
{
	size_t res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_recvmsg), "D" (sockfd), "S" (msg), "d" (flags));
	return res;
}

size_t
sendmsg(int sockfd, const struct msghdr *msg, int flags)
{
	size_t res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_sendmsg), "D" (sockfd), "S" (msg), "d" (flags));
	return res;
}

void
coroutine_bad_return_c(struct coroutine *cr)
{
	VG_(printf)("Coroutine returned unexpectedly!\n");
	VG_(printf)("(%s)\n", cr->name);
	VG_(tool_panic)((Char *)"Coroutine error");
}

void activate_bad_coroutine(struct coroutine *src, struct coroutine *dest)
{
	VG_(printf)("Activated bad coroutine!\n");
	VG_(printf)("(%s from %s)\n", dest->name, src->name);
	VG_(tool_panic)((Char *)"Coroutine error");
}

void deactivate_bad_coroutine(struct coroutine *src, struct coroutine *dest)
{
	VG_(printf)("Deactivated bad coroutine!\n");
	VG_(printf)("(%s for %s, src in use %ld)\n", src->name, dest->name,
		    src->in_use);
	VG_(tool_panic)((Char *)"Coroutine error");
}

static ULong
sysres_to_eax(SysRes sr)
{
	if (sr_isError(sr))
		return -sr_Err(sr);
	else
		return sr_Res(sr);
}

static Bool
op_binop(unsigned x)
{
	return x >= EXPR_BINOP_FIRST && x <= EXPR_BINOP_LAST;
}

static void
free_expression(const struct expression *e)
{
	if (!e)
		return;
	if (op_binop(e->type)) {
		free_expression(e->u.binop.arg1);
		free_expression(e->u.binop.arg2);
	} else {
		switch (e->type) {
		case EXPR_MEM:
			free_expression(e->u.mem.ptr);
			break;
		case EXPR_NOT:
			free_expression(e->u.unop.e);
			break;
		case EXPR_REG:
		case EXPR_CONST:
		case EXPR_IMPORTED:
			break;
		default:
			VG_(tool_panic)((Char *)"free bad expression");
		}
	}
	VG_(free)((void *)e);
}

static struct expression *
copy_expression(const struct expression *e)
{
	struct expression *work;
	work = VG_(malloc)("expression", sizeof(*work));
	*work = *e;
	work->type = e->type;
	if (op_binop(e->type)) {
		work->u.binop.arg1 = copy_expression(e->u.binop.arg1);
		work->u.binop.arg2 = copy_expression(e->u.binop.arg2);
	} else {
		switch (work->type) {
		case EXPR_REG:
		case EXPR_CONST:
		case EXPR_IMPORTED:
			break;
		case EXPR_MEM:
			work->u.mem.ptr = copy_expression(e->u.mem.ptr);
			break;
		case EXPR_NOT:
			work->u.unop.e = copy_expression(e->u.unop.e);
			break;
		default:
			VG_(tool_panic)((Char *)"Copy bad expression");
		}
	}
	return work;
}

static struct expression *
expr_reg(unsigned reg)
{
	struct expression *e;
	e = VG_(malloc)("expression", sizeof(*e));
	VG_(memset)(e, 0, sizeof(*e));
	e->type = EXPR_REG;
	e->u.reg = reg;
	return e;
}

static struct expression *
expr_const(unsigned long c)
{
	struct expression *e;
	e = VG_(malloc)("expression", sizeof(*e));
	VG_(memset)(e, 0, sizeof(*e));
	e->type = EXPR_CONST;
	e->u.cnst = c;
	return e;
}

static struct expression *
expr_mem(void *ptr, unsigned size)
{
	struct expression *e;
	e = VG_(malloc)("expression", sizeof(*e));
	VG_(memset)(e, 0, sizeof(*e));
	e->type = EXPR_MEM;
	e->u.mem.size = size;
	e->u.mem.ptr = ptr;
	return e;
}

#define expr_mem1(p) expr_mem((p), 1)
#define expr_mem2(p) expr_mem((p), 2)
#define expr_mem4(p) expr_mem((p), 4)
#define expr_mem8(p) expr_mem((p), 8)

static struct expression *
expr_not(struct expression *e)
{
	struct expression *r;
	r = VG_(malloc)("expression", sizeof(*r));
	VG_(memset)(r, 0, sizeof(*r));
	r->type = EXPR_NOT;
	r->u.unop.e = e;
	return r;
}

static struct expression *
expr_imported(void)
{
	struct expression *e;
	e = VG_(malloc)("expression", sizeof(*e));
	VG_(memset)(e, 0, sizeof(*e));
	e->type = EXPR_IMPORTED;
	return e;
}

static Bool
binop_commutes(unsigned op)
{
	switch (op) {
	case EXPR_AND: case EXPR_OR: case EXPR_EQ: case EXPR_XOR:
	case EXPR_MUL: case EXPR_MUL_HI: case EXPR_COMBINE:
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

static struct expression *
expr_binop(struct expression *e1, struct expression *e2, unsigned op)
{
	struct expression *e;

	if (e1->type == EXPR_CONST && e2->type == EXPR_CONST) {
		/* Try to do some constant folding.  We only do this
		   for a few special cases. */
		e = NULL;
		switch (op) {
		case EXPR_ADD:
			e = expr_const(e1->u.cnst + e2->u.cnst);
			break;
		default:
			break;
		}
		if (e) {
			free_expression(e1);
			free_expression(e2);
			return e;
		}
	}

	/* Do some basic canonicalisations first: if the operation is
	   commutative, the thing on the left always has a lower code
	   than the thing on the right. */
	if (binop_commutes(op) &&
	    e1->type > e2->type) {
		e = e1;
		e1 = e2;
		e2 = e;
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
		e = e2;
		e2 = e2->u.binop.arg2;
		VG_(free)(e);
	}

	if (binop_lident_0(op) &&
	    e1->type == EXPR_CONST &&
	    e1->u.cnst == 0) {
		free_expression(e1);
		return e2;
	}
	if (binop_rident_0(op) &&
	    e2->type == EXPR_CONST &&
	    e2->u.cnst == 0) {
		free_expression(e2);
		return e1;
	}
	e = VG_(malloc)("expression", sizeof(*e));
	VG_(memset)(e, 0, sizeof(*e));
	e->type = op;
	e->u.binop.arg1 = e1;
	e->u.binop.arg2 = e2;
	return e;
}

#define mk_expr(name1, name2)						\
	static inline struct expression *				\
	expr_ ## name1 (struct expression *e1, struct expression *e2)	\
	{								\
		return expr_binop(e1, e2, EXPR_ ## name2);		\
	}
mk_expr(sub, SUB)
mk_expr(add, ADD)
mk_expr(mul, MUL)
mk_expr(mul_hi, MUL_HI)
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

static void
send_expression(struct expression *e)
{
	VG_(printf)("WRITE ME %s\n", __func__);
}

static void
send_okay(void)
{
	struct response_message rsp;
	rsp.response = RESPONSE_OKAY;
	safeish_write(control_process_socket, &rsp, sizeof(rsp));
}

static void
send_error(void)
{
	struct response_message rsp;
	rsp.response = RESPONSE_ERR;
	safeish_write(control_process_socket, &rsp, sizeof(rsp));
}

static void
_send_ancillary(unsigned code, unsigned nr_args, const unsigned long *args)
{
	struct response_message rsp;
	struct response_ancillary anc;
	rsp.response = RESPONSE_ANCILLARY;
	anc.code = code;
	anc.nr_args = nr_args;
	safeish_write(control_process_socket, &rsp, sizeof(rsp));
	safeish_write(control_process_socket, &anc, sizeof(anc));
	safeish_write(control_process_socket, args, sizeof(args[0]) * nr_args);
}
#define send_ancillary(_code, ...)                         \
do {						           \
	const unsigned long args[] = {__VA_ARGS__};	   \
	_send_ancillary((_code),			   \
			sizeof(args)/sizeof(args[0]),	   \
			args);				   \
} while (0)

static void
send_string(unsigned size, const void *buf)
{
	struct response_message msg;
	struct response_string rs;
	msg.response = RESPONSE_STRING;
	rs.len = size;
	safeish_write(control_process_socket, &msg, sizeof(msg));
	safeish_write(control_process_socket, &rs, sizeof(rs));
	safeish_write(control_process_socket, buf, size);
}

static void
get_control_command(struct control_command *cmd)
{
	struct command_header ch;
	safeish_read(control_process_socket, &ch, sizeof(ch));
	cmd->cmd = ch.command;
	switch (ch.command) {
	case WORKER_SNAPSHOT:
	case WORKER_KILL:
	case WORKER_THREAD_STATE:
	case WORKER_REPLAY_STATE:
		tl_assert(ch.nr_args == 0);
		return;
	case WORKER_RUN:
		tl_assert(ch.nr_args == 1);
		safeish_read(control_process_socket, &cmd->u.run.nr, 8);
		break;
	case WORKER_TRACE:
		tl_assert(ch.nr_args == 1);
		safeish_read(control_process_socket, &cmd->u.trace.nr, 8);
		break;
	case WORKER_CONTROL_TRACE:
		tl_assert(ch.nr_args == 1);
		safeish_read(control_process_socket, &cmd->u.control_trace.nr, 8);
		break;
	case WORKER_TRACE_THREAD:
		tl_assert(ch.nr_args == 1);
		safeish_read(control_process_socket, &cmd->u.trace_thread.thread, 8);
		break;
	case WORKER_TRACE_ADDRESS:
		tl_assert(ch.nr_args == 1);
		safeish_read(control_process_socket, &cmd->u.trace_mem.address, 8);
		break;
	case WORKER_RUNM:
		tl_assert(ch.nr_args == 2);
		safeish_read(control_process_socket, &cmd->u.runm.thread, 8);
		safeish_read(control_process_socket, &cmd->u.runm.nr, 8);
		break;
	default:
		VG_(tool_panic)((Char *)"bad worker command");
	}
	return;
}

#define _TRACE(code, args...)                             \
	send_ancillary(ANCILLARY_TRACE_ ## code,	  \
		       record_nr,			  \
		       access_nr,			  \
		       current_thread->id,		  \
		       ## args)

#define TRACE(code, args...)				  \
	do {						  \
		if (trace_mode) _TRACE(code, ## args);	  \
	} while (0)


/* Bits for managing the transitions between client code and the
   replay monitor. */

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
	switch (offset) {
	case OFFSET_amd64_RAX:
		return &state->rax;
	case OFFSET_amd64_RCX:
		return &state->rcx;
	case OFFSET_amd64_RDX:
		return &state->rdx;
	case OFFSET_amd64_RBX:
		return &state->rbx;
	case OFFSET_amd64_RSP:
		return &state->rsp;
	case OFFSET_amd64_RBP:
		return &state->rbp;
	case OFFSET_amd64_RSI:
		return &state->rsi;
	case OFFSET_amd64_RDI:
		return &state->rdi;
	case OFFSET_amd64_R8:
		return &state->r8;
	case OFFSET_amd64_R9:
		return &state->r9;
	case OFFSET_amd64_R10:
		return &state->r10;
	case OFFSET_amd64_R11:
		return &state->r11;
	case OFFSET_amd64_R12:
		return &state->r12;
	case OFFSET_amd64_R13:
		return &state->r13;
	case OFFSET_amd64_R14:
		return &state->r14;
	case OFFSET_amd64_R15:
		return &state->r15;
	case OFFSET_amd64_CC_OP:
		return &state->cc_op;
	case OFFSET_amd64_CC_DEP1:
		return &state->cc_dep1;
	case OFFSET_amd64_CC_DEP2:
		return &state->cc_dep2;
	case OFFSET_amd64_CC_NDEP:
		return &state->cc_ndep;
	case 160:
		return &state->d_flag;
	case 168:
		return &state->rip;
	case 184:
		return &state->fs_zero;
	case 200:
		return &state->xmm0;
	case 216:
		return &state->xmm1;
	default:
		VG_(printf)("Bad state offset %d\n", offset);
		VG_(tool_panic)((Char *)"failed");
		break;
	}
}

static void
copy_aiv(struct abstract_interpret_value *dest,
	 const struct abstract_interpret_value *src)
{
	dest->v1 = src->v1;
	dest->v2 = src->v2;
	free_expression(dest->origin);
	dest->origin = copy_expression(src->origin);
	free_expression(dest->origin2);
	if (src->origin2)
		dest->origin2 = copy_expression(src->origin2);
	else
		dest->origin2 = NULL;
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

	VG_(memcpy)((void *)ptr, &data.v1, size);
}

static struct expression *
find_origin_expression(struct interpret_mem_lookaside *iml,
		       unsigned size,
		       unsigned long addr)
{
	while (iml) {
		if (iml->ptr == addr && iml->size == size)
			return copy_expression(iml->aiv.origin);
		if (iml->ptr <= addr && iml->ptr + iml->size >= addr + size) {
			unsigned long mask;
			switch (size) {
			case 1: mask = 0xff; break;
			case 2: mask = 0xffff; break;
			case 4: mask = 0xffffffff; break;
			default: ASSUME(0);
			}
			return expr_and(expr_shrl(copy_expression(iml->aiv.origin),
						  expr_const((addr - iml->ptr) * 8)),
					expr_const(mask));
		}
		if (iml->ptr < addr + size &&
		    iml->ptr + iml->size > addr) {
			return expr_combine(copy_expression(iml->aiv.origin),
					    find_origin_expression(iml->next, size, addr));
		}
		iml = iml->next;
	}
	return expr_imported();
}

static void
interpreter_do_load(struct abstract_interpret_value *aiv,
		    unsigned size,
		    unsigned long addr)
{
	free_expression(aiv->origin);
	VG_(memcpy)(&aiv->v1, (const void *)addr, size);
	aiv->origin = find_origin_expression(head_interpret_mem_lookaside,
					     size,
					     addr);
}

static void
eval_expression(struct interpret_state *state,
		struct abstract_interpret_value *dest,
		IRExpr *expr);

/* generalised left-shifter */
static inline Long lshift ( Long x, Int n )
{
   if (n >= 0)
      return x << n;
   else
      return x >> (-n);
}


static void
do_ccall_calculate_condition(struct interpret_state *state,
			     struct abstract_interpret_value *dest,
			     IRCallee *cee,
			     IRType retty,
			     IRExpr **args)
{
	struct abstract_interpret_value condcode = {};
	struct abstract_interpret_value op = {};
	struct abstract_interpret_value dep1 = {};
	struct abstract_interpret_value dep2 = {};
	struct abstract_interpret_value ndep = {};
	int inv;

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(state, &condcode, args[0]);
	tl_assert(condcode.origin->type == EXPR_CONST);
	free_expression(condcode.origin);

	eval_expression(state, &op, args[1]);
	tl_assert(op.origin->type == EXPR_CONST);
	free_expression(op.origin);

	eval_expression(state, &dep1, args[2]);
	eval_expression(state, &dep2, args[3]);
	eval_expression(state, &ndep, args[4]);
	inv = condcode.v1 & 1;
	switch (condcode.v1 & ~1) {
	case AMD64CondZ:
		switch (op.v1) {
		case AMD64G_CC_OP_LOGICQ:
			dest->v1 = dep1.v1 == 0;
			free_expression(dest->origin);
			dest->origin = copy_expression(dep1.origin);
			break;
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBQ:
			dest->v1 = dep1.v1 == dep2.v1;
			free_expression(dest->origin);
			dest->origin = expr_eq(copy_expression(dep1.origin),
					       copy_expression(dep2.origin));
			break;
		case AMD64G_CC_OP_INCQ:
			dest->v1 = dep1.v1 == 0;
			free_expression(dest->origin);
			dest->origin = expr_eq(copy_expression(dep1.origin),
					       expr_const(0));
			break;
		default:
			VG_(printf)("Strange operation code %ld\n", op.v1);
			VG_(tool_panic)((Char *)"failed");
		}
		break;
	case AMD64CondLE:
		switch (op.v1) {
		case AMD64G_CC_OP_SUBB:
			dest->v1 = (signed char)dep1.v1 <= (signed char)dep2.v1;
			free_expression(dest->origin);
			dest->origin =
				expr_be(expr_and(expr_add(copy_expression(dep1.origin),
							  expr_const(0x80)),
						 expr_const(0xff)),
					expr_and(expr_add(copy_expression(dep2.origin),
							  expr_const(0x80)),
						 expr_const(0xff)));
			break;
		case AMD64G_CC_OP_SUBQ:
			dest->v1 = (long)dep1.v1 <= (long)dep2.v1;
			free_expression(dest->origin);
			dest->origin = expr_le(copy_expression(dep1.origin),
					       copy_expression(dep2.origin));
			break;
		default:
			VG_(printf)("Strange operation code %ld for le\n", op.v1);
			VG_(tool_panic)((Char *)"failed");
		}
		break;
	case AMD64CondB:
		switch (op.v1) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->v1 = dep1.v1 < dep2.v1;
			free_expression(dest->origin);
			dest->origin = expr_b(copy_expression(dep1.origin),
					      copy_expression(dep2.origin));
			break;
		case AMD64G_CC_OP_ADDQ:
			dest->v1 = dep1.v1 + dep2.v1 < dep1.v1;
			free_expression(dest->origin);
			dest->origin = expr_b(expr_add(copy_expression(dep1.origin),
						       copy_expression(dep2.origin)),
					      copy_expression(dep1.origin));
			break;
		default:
			VG_(printf)("Strange operation code %ld for b\n", op.v1);
			VG_(tool_panic)((Char *)"failed");
		}
		break;
	case AMD64CondBE:
		switch (op.v1) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->v1 = dep1.v1 <= dep2.v1;
			free_expression(dest->origin);
			dest->origin = expr_be(copy_expression(dep1.origin),
					       copy_expression(dep2.origin));
			break;
		default:
			VG_(printf)("Strange operation code %ld for be\n", op.v1);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	case AMD64CondS:
		switch (op.v1) {
		case AMD64G_CC_OP_LOGICL:
			dest->v1 = dep1.v1 >> 31;
			free_expression(dest->origin);
			dest->origin = expr_shrl(copy_expression(dep1.origin),
						 expr_const(31));
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->v1 = dep1.v1 >> 63;
			free_expression(dest->origin);
			dest->origin = expr_shrl(copy_expression(dep1.origin),
						 expr_const(63));
			break;
		default:
			VG_(printf)("Strange operation code %ld for s\n", op.v1);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	default:
		VG_(printf)("Strange cond code %ld (op %ld)\n", condcode.v1, op.v1);
		VG_(tool_panic)((Char *)"failed");
	}
	free_expression(dep1.origin);
	free_expression(dep2.origin);
	free_expression(ndep.origin);

	if (inv) {
		dest->v1 ^= 1;
		dest->origin = expr_not(dest->origin);
	}
}

static void
do_ccall_calculate_rflags_c(struct interpret_state *state,
			    struct abstract_interpret_value *dest,
			    IRCallee *cee,
			    IRType retty,
			    IRExpr **args)
{
	struct abstract_interpret_value op = {};
	struct abstract_interpret_value dep1 = {};
	struct abstract_interpret_value dep2 = {};
	struct abstract_interpret_value ndep = {};

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(state, &op, args[0]);
	tl_assert(op.origin->type == EXPR_CONST);
	free_expression(op.origin);

	eval_expression(state, &dep1, args[1]);
	eval_expression(state, &dep2, args[2]);
	eval_expression(state, &ndep, args[3]);

	switch (op.v1) {
	case AMD64G_CC_OP_SUBB:
		dest->v1 = (unsigned char)(dep1.v1 - dep2.v1) < (unsigned char)dep2.v1;
		free_expression(dest->origin);
		dest->origin = expr_b(expr_and(expr_sub(copy_expression(dep1.origin),
							copy_expression(dep2.origin)),
					       expr_const(0xff)),
				      expr_and(copy_expression(dep2.origin),
					       expr_const(0xff)));
		break;

	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICL:
		/* XXX Why doesn't the Valgrind optimiser remove
		 * these? */
		dest->v1 = 0;
		free_expression(dest->origin);
		dest->origin = expr_const(0);
		break;

	default:
		VG_(printf)("Can't calculate C flags for op %ld\n",
			    op.v1);
		VG_(tool_panic)((Char *)"dead");
	}

	free_expression(dep1.origin);
	free_expression(dep2.origin);
	free_expression(ndep.origin);
}

static void
do_ccall_generic(struct interpret_state *state, struct abstract_interpret_value *dest,
		 IRCallee *cee, IRType retty, IRExpr **args)
{
	struct abstract_interpret_value rargs[6];
	unsigned x;

	tl_assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(state, &rargs[x], args[x]);
	}
	dest->v1 = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				       unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].v1, rargs[1].v1, rargs[2].v1, rargs[3].v1, rargs[4].v1,
		 rargs[5].v1);
	dest->v2 = 0;
	free_expression(dest->origin);
	free_expression(dest->origin2);
	dest->origin2 = NULL;
	dest->origin = rargs[0].origin;
	for (x = 1; args[x]; x++)
		dest->origin = expr_combine(dest->origin, rargs[x].origin);
}

static void
do_ccall(struct interpret_state *state,
	 struct abstract_interpret_value *dest,
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

static void load_event(const void *ptr, unsigned size, void *read_bytes,
		       unsigned long rsp);
static void
eval_expression(struct interpret_state *state,
		struct abstract_interpret_value *dest,
		IRExpr *expr)
{
#define ORIGIN(x)				\
	do {					\
		struct expression *t;		\
		t = dest->origin;		\
		dest->origin = x;		\
		free_expression(t);		\
	} while (0)

	tl_assert(expr != NULL);

	switch (expr->tag) {
	case Iex_Get: {
		struct abstract_interpret_value *src;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src = get_aiv_for_offset(state,
					 expr->Iex.Get.offset - sub_word_offset);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
		case Ity_V128:
			tl_assert(!sub_word_offset);
			copy_aiv(dest, src);
			break;
		case Ity_I32:
			tl_assert(!(sub_word_offset % 4));
			dest->v1 = (src->v1 >> (sub_word_offset * 8)) & 0xffffffff;
			free_expression(dest->origin);
			free_expression(dest->origin2);
			dest->origin2 = NULL;
			dest->origin = expr_and(expr_const(0xffffffff),
						expr_shrl(copy_expression(src->origin),
							  expr_const(sub_word_offset * 8)));
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->v1 = (src->v1 >> (sub_word_offset * 8)) & 0xffff;
			free_expression(dest->origin);
			free_expression(dest->origin2);
			dest->origin2 = NULL;
			dest->origin = expr_and(expr_const(0xffff),
						expr_shrl(copy_expression(src->origin),
							  expr_const(sub_word_offset * 8)));
			break;
		case Ity_I8:
			dest->v1 = (src->v1 >> (sub_word_offset * 8)) & 0xff;
			free_expression(dest->origin);
			free_expression(dest->origin2);
			dest->origin2 = NULL;
			dest->origin = expr_and(expr_const(0xff),
						expr_shrl(copy_expression(src->origin),
							  expr_const(sub_word_offset * 8)));
			break;
		default:
			VG_(tool_panic)((Char *)"bad get type");
		}
		break;
	}

	case Iex_RdTmp:
		copy_aiv(dest, &state->temporaries[expr->Iex.RdTmp.tmp]);
		break;

	case Iex_Const: {
		IRConst *cnst = expr->Iex.Const.con;
		free_expression(dest->origin);
		dest->origin = NULL;
		free_expression(dest->origin2);
		dest->origin2 = NULL;
		switch (cnst->tag) {
		case Ico_U1:
			dest->v1 = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->v1 = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->v1 = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->v1 = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->v1 = cnst->Ico.U64;
			break;
		case Ico_V128:
			dest->v1 = cnst->Ico.V128;
			dest->v1 = dest->v1 | (dest->v1 << 16) | (dest->v1 << 32) | (dest->v1 << 48);
			dest->v2 = dest->v1;
			dest->origin2 = expr_const(dest->v2);
			break;
		default:
			ASSUME(0);
		}
		dest->origin = expr_const(dest->v1);
		break;
	}

	case Iex_Binop: {
		struct abstract_interpret_value arg1 = {0};
		struct abstract_interpret_value arg2 = {0};
		eval_expression(state, &arg1, expr->Iex.Binop.arg1);
		eval_expression(state, &arg2, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			dest->v1 = arg1.v1 - arg2.v1;
			ORIGIN(expr_sub(arg1.origin, arg2.origin));
			break;
		case Iop_Sub32:
			dest->v1 = (arg1.v1 - arg2.v1) & 0xffffffff;
			ORIGIN(expr_and(expr_sub(arg1.origin, arg2.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Sub8:
			dest->v1 = (arg1.v1 - arg2.v1) & 0xff;
			ORIGIN(expr_and(expr_sub(arg1.origin, arg2.origin),
					expr_const(0xff)));
			break;
		case Iop_Add64:
			dest->v1 = arg1.v1 + arg2.v1;
			ORIGIN(expr_add(arg1.origin, arg2.origin));
			break;
		case Iop_Add32:
			dest->v1 = (arg1.v1 + arg2.v1) & 0xffffffff;
			ORIGIN(expr_and(expr_add(arg1.origin, arg2.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And8:
			dest->v1 = arg1.v1 & arg2.v1;
			ORIGIN(expr_and(arg1.origin, arg2.origin));
			break;
		case Iop_Or8:
		case Iop_Or32:
		case Iop_Or64:
			dest->v1 = arg1.v1 | arg2.v1;
			ORIGIN(expr_or(arg1.origin, arg2.origin));
			break;
		case Iop_Shl32:
			dest->v1 = (arg1.v1 << arg2.v1) & 0xffffffff;
			ORIGIN(expr_and(expr_shl(arg1.origin, arg2.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Shl64:
			dest->v1 = arg1.v1 << arg2.v1;
			ORIGIN(expr_shl(arg1.origin, arg2.origin));
			break;
		case Iop_Sar64:
			dest->v1 = (long)arg1.v1 >> arg2.v1;
			ORIGIN(expr_shra(arg1.origin, arg2.origin));
			break;
		case Iop_Shr64:
			dest->v1 = arg1.v1 >> arg2.v1;
			ORIGIN(expr_shrl(arg1.origin, arg2.origin));
			break;
		case Iop_Xor64:
		case Iop_Xor32:
			dest->v1 = arg1.v1 ^ arg2.v1;
			ORIGIN(expr_xor(arg1.origin, arg2.origin));
			break;
		case Iop_CmpNE8:
			dest->v1 = arg1.v1 != arg2.v1;
			ORIGIN(expr_not(expr_eq(arg1.origin, arg2.origin)));
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->v1 = arg1.v1 == arg2.v1;
			ORIGIN(expr_eq(arg1.origin, arg2.origin));
			break;
		case Iop_CmpNE64:
			dest->v1 = arg1.v1 != arg2.v1;
			ORIGIN(expr_not(expr_eq(arg1.origin, arg2.origin)));
			break;
		case Iop_CmpLE64U:
			dest->v1 = arg1.v1 <= arg2.v1;
			ORIGIN(expr_be(arg1.origin, arg2.origin));
			break;
		case Iop_CmpLE64S:
			dest->v1 = (long)arg1.v1 <= (long)arg2.v1;
			ORIGIN(expr_le(arg1.origin, arg2.origin));
			break;
		case Iop_CmpLT64U:
			dest->v1 = arg1.v1 < arg2.v1;
			ORIGIN(expr_b(arg1.origin, arg2.origin));
			break;
		case Iop_Mul64:
			dest->v1 = arg1.v1 * arg2.v1;
			ORIGIN(expr_mul(arg1.origin, arg2.origin));
			break;
		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			struct expression *t1, *t2;
			dest->v1 = arg1.v1 * arg2.v1;
			a1 = arg1.v1 & 0xffffffff;
			a2 = arg1.v1 >> 32;
			b1 = arg2.v1 & 0xffffffff;
			b2 = arg2.v1 >> 32;
			dest->v2 = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32)) >> 32);
			VG_(printf)("%lx * %lx -> %lx:%lx\n",
				    arg1.v1, arg2.v1, dest->v1, dest->v2);
			t1 = dest->origin;
			t2 = dest->origin2;
			dest->origin = expr_mul(arg1.origin, arg2.origin);
			dest->origin2 = expr_mul_hi(arg1.origin, arg2.origin);
			free_expression(t1);
			free_expression(t2);
			break;
		}
		case Iop_32HLto64:
			dest->v1 = (arg1.v1 << 32) | arg1.v2;
			ORIGIN(expr_or(expr_shl(arg1.origin,
						expr_const(32)),
				       arg2.origin));
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->v1 = arg2.v1;
			dest->v2 = arg1.v1;
			free_expression(dest->origin);
			free_expression(dest->origin2);
			dest->origin = arg2.origin;
			dest->origin2 = arg1.origin;
			break;

		case Iop_DivModU128to64:
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			asm ("div %4\n"
			     : "=a" (dest->v1), "=d" (dest->v2)
			     : "0" (arg1.v1), "1" (arg1.v2), "r" (arg2.v1));
			free_expression(dest->origin);
			free_expression(dest->origin2);
			dest->origin = expr_combine(arg1.origin,
						    expr_combine(arg1.origin2,
								 arg2.origin));
			dest->origin2 = copy_expression(dest->origin);
			break;

		default:
			VG_(tool_panic)((Char *)"bad binop");
		}
		break;
	}

	case Iex_Unop: {
		struct abstract_interpret_value arg = {0};
		eval_expression(state, &arg, expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->v1 = arg.v1 >> 32;
			ORIGIN(expr_shrl(arg.origin, expr_const(32)));
			break;
		case Iop_64to32:
			dest->v1 = arg.v1 & 0xffffffff;
			ORIGIN(expr_and(arg.origin, expr_const(0xfffffffful)));
			break;
		case Iop_64to16:
			dest->v1 = arg.v1 & 0xffff;
			ORIGIN(expr_and(arg.origin, expr_const(0xffff)));
			break;
		case Iop_64to8:
			dest->v1 = arg.v1 & 0xff;
			ORIGIN(expr_and(arg.origin, expr_const(0xff)));
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->v1 = arg.v1;
			ORIGIN(arg.origin);
			break;
		case Iop_64to1:
			dest->v1 = arg.v1 & 1;
			ORIGIN(expr_and(arg.origin, expr_const(1)));
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
			dest->v1 = (long)(int)arg.v1;
			ORIGIN(expr_shra(expr_shl(arg.origin,
						  expr_const(32)),
					 expr_const(32)));
			break;
		case Iop_8Sto32:
			dest->v1 = (int)(signed char)arg.v1;
			ORIGIN(expr_shra(expr_shl(arg.origin,
						  expr_const(56)),
					 expr_const(56)));
			break;
		case Iop_128HIto64:
			dest->v1 = arg.v2;
			tl_assert(arg.origin2 != NULL);
			ORIGIN(arg.origin2);
			break;

		case Iop_Not1:
			dest->v1 = !arg.v1;
			ORIGIN(expr_and(expr_not(arg.origin),
					expr_const(1)));
			break;

		case Iop_Not32:
			dest->v1 = ~arg.v1 & 0xffffffff;
			ORIGIN(expr_and(expr_not(arg.origin),
					expr_const(0xffffffff)));
			break;

		case Iop_Not64:
			dest->v1 = ~arg.v1;
			ORIGIN(expr_not(arg.origin));
			break;

		default:
			VG_(tool_panic)((Char *)"bad unop");
		}
		break;
	}

	case Iex_Load: {
		struct abstract_interpret_value addr = {0};
		struct abstract_interpret_value data = {0};
		unsigned char dummy_buf[16];

		eval_expression(state, &addr, expr->Iex.Load.addr);
		interpreter_do_load(&data,
				    sizeofIRType(expr->Iex.Load.ty),
				    addr.v1);
		dest->v1 = data.v1;
		ORIGIN(expr_combine(addr.origin, data.origin));

		load_event((const void *)addr.v1,
			   sizeofIRType(expr->Iex.Load.ty),
			   dummy_buf,
			   state->rsp.v1);
		break;
	}
	case Iex_Mux0X: {
		struct abstract_interpret_value cond = {0};
		struct abstract_interpret_value res0 = {0};
		struct abstract_interpret_value resX = {0};
		eval_expression(state, &cond, expr->Iex.Mux0X.cond);
		eval_expression(state, &res0, expr->Iex.Mux0X.expr0);
		eval_expression(state, &resX, expr->Iex.Mux0X.exprX);
		if (cond.v1 == 0) {
			dest->v1 = res0.v1;
			ORIGIN(expr_combine(cond.origin, res0.origin));
			free_expression(resX.origin);
		} else {
			dest->v1 = resX.v1;
			ORIGIN(expr_combine(cond.origin, resX.origin));
			free_expression(res0.origin);
		}
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

static void commit_interpreter_state(void);
static void initialise_interpreter_state(void);

/* XXX We don't track dependencies through dirty calls at all.  Oh
 * well. */
static void
do_dirty_call(struct interpret_state *is,
	      VexGuestArchState *state,
	      IRSB *irsb,
	      IRDirty *details)
{
	struct abstract_interpret_value guard = {0};
	struct abstract_interpret_value arg = {0};
	unsigned long args[6];
	unsigned x;
	unsigned long res;

	if (details->guard) {
		eval_expression(is, &guard, details->guard);
		free_expression(guard.origin);
		if (!guard.v1)
			return;
	}
	for (x = 0; details->args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(is, &arg, details->args[x]);
		free_expression(arg.origin);
		args[x] = arg.v1;
	}
	tl_assert(!details->cee->regparms);

	commit_interpreter_state();

	if (details->needsBBP) {
		res = ((unsigned long (*)(VexGuestArchState *,
					  unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long))(details->cee->addr))
			(state, args[0], args[1], args[2], args[3],
			 args[4], args[5]);
	} else {
		res = ((unsigned long (*)(unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long,
					  unsigned long))(details->cee->addr))
			(args[0], args[1], args[2], args[3],
			 args[4], args[5]);
	}

	initialise_interpreter_state();

	if (details->tmp != IRTemp_INVALID) {
		is->temporaries[details->tmp].v1 = res;
		free_expression(is->temporaries[details->tmp].origin);
		is->temporaries[details->tmp].origin =
			expr_imported();
	}
}

static void initialise_is_for_vex_state(struct interpret_state *is,
					const VexGuestArchState *state);
static void syscall_event(VexGuestAMD64State *state);
static void footstep_event(Addr rip, Word rdx, Word rcx, Word rax);
static void store_event(void *ptr, unsigned size, const void *written_bytes,
			unsigned long rsp);

static UInt
interpret_log_control_flow(VexGuestArchState *state)
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
	unsigned x;

	addr = istate->rip.v1;
	if (addr == 0) {
		/* Hackity hackity hack: at the start of day, RIP in
		   the interpreter state is wrong.  Fix it up a
		   bit. */
		initialise_is_for_vex_state(istate, state);
		addr = state->guest_RIP;
	}
	VG_(printf)("Interpreting from rip %llx\n", addr);

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

	tl_assert(istate->temporaries == NULL);
	istate->temporaries = VG_(malloc)("interpreter temporaries",
					  sizeof(istate->temporaries[0]) *
					  irsb->tyenv->types_used);
	VG_(memset)(istate->temporaries,
		    0,
		    sizeof(istate->temporaries[0]) *
		    irsb->tyenv->types_used);
	for (stmt_nr = 0; stmt_nr < irsb->stmts_used; stmt_nr++) {
		stmt = irsb->stmts[stmt_nr];
		VG_(printf)("Interpreting ");
		ppIRStmt(stmt);
		VG_(printf)("\n");
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			footstep_event(stmt->Ist.IMark.addr,
				       istate->rdx.v1,
				       istate->rcx.v1,
				       istate->rax.v1);
			break;
		case Ist_AbiHint:
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
			struct abstract_interpret_value tmp = {0};
			switch (typeOfIRExpr(irsb->tyenv, stmt->Ist.Put.data)) {
			case Ity_I8:
				eval_expression(istate, &tmp, stmt->Ist.Put.data);
				dest->v1 &= ~(0xFF << (byte_offset * 8));
				dest->v1 |= tmp.v1 << (byte_offset * 8);
				dest->origin =
					expr_or( expr_shl(tmp.origin,
							  expr_const(byte_offset * 8)),
						 expr_and(dest->origin,
							  expr_const(~(0xFF << (byte_offset * 8)))));
				break;
			case Ity_I64:
			case Ity_I128:
			case Ity_V128:
				tl_assert(byte_offset == 0);
				eval_expression(istate, dest, stmt->Ist.Put.data);
				break;
			default:
				VG_(tool_panic)((Char *)"put to strange-sized location");
			}
			break;
		}
		case Ist_Store: {
			/* In principle, we should probably make
			   everything depend on addr on at this point,
			   because the write could clobber almost
			   anything.  We don't because that's not
			   usually useful, and it tends to hide lots
			   of more interesting dependencies. */
			struct abstract_interpret_value addr = {0};
			struct abstract_interpret_value data = {0};
			eval_expression(istate, &addr, stmt->Ist.Store.addr);
			eval_expression(istate, &data, stmt->Ist.Store.data);
			interpret_create_mem_lookaside(
				addr.v1,
				sizeofIRType(
					typeOfIRExpr(irsb->tyenv,
						     stmt->Ist.Store.data)),
				data);
			free_expression(addr.origin);

			store_event((void *)addr.v1,
				    sizeofIRType(typeOfIRExpr(irsb->tyenv,
							      stmt->Ist.Store.data)),
				    &data.v1,
				    istate->rsp.v1);
			break;
		}

		case Ist_Dirty: {
			do_dirty_call(istate, state, irsb, stmt->Ist.Dirty.details);
			break;
		}

		case Ist_Exit: {
			struct abstract_interpret_value guard = {0};
			if (stmt->Ist.Exit.guard) {
				eval_expression(istate, &guard, stmt->Ist.Exit.guard);
				send_expression(guard.origin);
				free_expression(guard.origin);
				if (!guard.v1)
					break;
			}
			tl_assert(stmt->Ist.Exit.jk == Ijk_Boring);
			tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
			istate->rip.v1 = stmt->Ist.Exit.dst->Ico.U64;
			goto finished_block;
		}

		default:
			VG_(printf)("Don't know how to interpret statement\n");
			ppIRStmt(stmt);
			break;
		}
	}

	tl_assert(irsb->jumpkind == Ijk_Boring ||
		  irsb->jumpkind == Ijk_Call ||
		  irsb->jumpkind == Ijk_Ret ||
		  irsb->jumpkind == Ijk_Sys_syscall);

	{
		struct abstract_interpret_value next_addr = {0};
		eval_expression(istate, &next_addr, irsb->next);
		send_expression(next_addr.origin);
		free_expression(next_addr.origin);
		istate->rip.v1 = next_addr.v1;
	}

	if (irsb->jumpkind == Ijk_Sys_syscall) {
		commit_interpreter_state();
		syscall_event(state);
		initialise_interpreter_state();
	}

finished_block:
	VG_(printf)("Returning from interpreter.\n");
	for (x = 0; x < irsb->tyenv->types_used; x++) {
		free_expression(istate->temporaries[x].origin);
	}
	VG_(free)(istate->temporaries);
	istate->temporaries = NULL;

	state->guest_RIP = istate->rip.v1;

	return VG_TRC_BORING;
}

/* Run the client thread until it generates an event, and figure out
   what that event was. */
static void
run_thread(struct replay_thread *rt, struct client_event_record *cer,
	   Bool trace_control)
{
	static ThreadId last_run;

	tl_assert(!VG_(in_generated_code));
	tl_assert(client_event == NULL);
	tl_assert(current_thread == NULL);
	tl_assert(VG_(running_tid) == VG_INVALID_THREADID);
	tl_assert(!rt->dead);

	last_run = rt->id;
	cer->type = EVENT_nothing;
	current_thread = rt;
	client_event = cer;
	VG_(running_tid) = rt->id;

	if (trace_control) {
		VG_(interpret) = interpret_log_control_flow;
	} else {
		VG_(interpret) = NULL;
	}
	run_coroutine(&replay_machine,
		      &rt->coroutine,
		      "run_thread");

	tl_assert(cer == client_event);
	tl_assert(rt == current_thread);
	client_event = NULL;
	current_thread = NULL;
	VG_(running_tid) = VG_INVALID_THREADID;

	tl_assert(cer->type != EVENT_nothing);
	tl_assert(!VG_(in_generated_code));
}

/* Something happened in the client which requires the monitor to do
   something. */
static void
_client_event(void)
{
	tl_assert(VG_(in_generated_code));
	VG_(in_generated_code) = False;
	run_coroutine(&current_thread->coroutine,
		      &replay_machine,
		      "_client_event");
	tl_assert(VG_(running_tid) == current_thread->id);
	VG_(in_generated_code) = True;
}
#define event(_code, ...)					  \
do {                                                              \
	unsigned long args[] = {__VA_ARGS__};			  \
	client_event->type = (_code);                             \
	client_event->nr_args = sizeof(args) / sizeof(args[0]);   \
	client_event->args = args;                                \
	_client_event();                                          \
} while (0)

/* The various events.  These are the bits which run in client
   context. */
static void
footstep_event(Addr rip, Word rdx, Word rcx, Word rax)
{
	if (!current_thread->in_monitor) {
		TRACE(FOOTSTEP, rip, rdx, rcx, rax);
		if (use_footsteps)
			event(EVENT_footstep, rip, rdx, rcx, rax);
	}
}

static void
syscall_event(VexGuestAMD64State *state)
{
	/* This needs to be kept in sync with the variant at the end
	   of interpret_log_control_flow() */
	if (current_thread->in_monitor) {
		VG_(client_syscall)(VG_(running_tid), VEX_TRC_JMP_SYS_SYSCALL);
	} else {
		TRACE(SYSCALL, state->guest_RAX);
		event(EVENT_syscall, state->guest_RAX, state->guest_RDI,
		      state->guest_RSI, state->guest_RDX, (unsigned long)state);
	}
}

static ULong
rdtsc_event(void)
{
	if (current_thread->in_monitor) {
		/* This is obviously non-deterministic.  We rely on
		   the in-client monitor code to do the right
		   thing. */
		unsigned eax, edx;
		__asm__ __volatile__("rdtsc" : "=a" (eax), "=d" (edx));
		return (((ULong)edx) << 32) | ((ULong)eax);
	} else {
		TRACE(RDTSC);
		event(EVENT_rdtsc);
		return current_thread->rdtsc_result;
	}
}

static void
load_event(const void *ptr, unsigned size, void *read_bytes,
	   unsigned long rsp)
{
	VG_(memcpy)(read_bytes, ptr, size);
	if (IS_STACK(ptr, rsp))
		return;
	if ( (ptr <= (const void *)trace_address &&
	      ptr + size > (const void *)trace_address) ||
	    (trace_mode && !current_thread->in_monitor))
		_TRACE(LOAD,
		       size == 8 ?
		       *(unsigned long *)read_bytes :
		       *(unsigned long *)read_bytes & ((1ul << (size * 8)) - 1),
		       size,
		       (unsigned long)ptr,
		       current_thread->in_monitor);
	if (!current_thread->in_monitor) {
		access_nr++;
		event(EVENT_load, (unsigned long)ptr, size,
		      (unsigned long)read_bytes);
	}
}

static void
store_event(void *ptr, unsigned size, const void *written_bytes,
	    unsigned long rsp)
{
	VG_(memcpy)(ptr, written_bytes, size);
	if (IS_STACK(ptr, rsp))
		return;
	if ( (ptr <= (const void *)trace_address &&
	      ptr + size > (const void *)trace_address) ||
	    (trace_mode && !current_thread->in_monitor))
		_TRACE(STORE,
		       size == 8 ?
		       *(unsigned long *)written_bytes :
		       *(unsigned long *)written_bytes & ((1ul << (size * 8)) - 1),
		       size,
		       (unsigned long)ptr,
		       current_thread->in_monitor);
	if (!current_thread->in_monitor) {
		access_nr++;
		event(EVENT_store, (unsigned long)ptr, size,
		      (unsigned long)written_bytes);
	}
}

static Bool
client_request_event(ThreadId tid, UWord *arg_block, UWord *ret)
{
	if (VG_IS_TOOL_USERREQ('P', 'P', arg_block[0])) {
		/* We are in generated code here, despite what
		   Valgrind might think about it. */
		VG_(in_generated_code) = True;
		if (trace_mode) {
			if (arg_block[0] == VG_USERREQ_PPRES_CALL_LIBRARY)
				_TRACE(CALLING);
			else
				_TRACE(CALLED);
			send_string(VG_(strlen)((Char *)arg_block[1]),
				    (const char *)arg_block[1]);
		}
		event(EVENT_client_request, arg_block[0], arg_block[1]);
		VG_(in_generated_code) = False;
		*ret = 0;
		return True;
	} else if (VG_IS_TOOL_USERREQ('E', 'A', arg_block[0])) {
		if ((arg_block[0] & 0xffff) == 0) {
			TRACE(ENTER_MONITOR);
			current_thread->in_monitor = True;
		} else {
			TRACE(EXIT_MONITOR);
			current_thread->in_monitor = False;
		}
		*ret = 0;
		return True;
	} else {
		return False;
	}
}

#define included_for_replay
#include "transform_expr.c"


static struct replay_thread *
get_thread_by_id(ThreadId id)
{
	struct replay_thread *rt;
	for (rt = head_thread; rt && rt->id != id; rt = rt->next)
		;
	return rt;
}

static void
do_trace_thread_command(long thread)
{
	struct replay_thread *rt;
	struct client_event_record cer;

	rt = get_thread_by_id(thread);
	if (!rt) {
		VG_(printf)("Couldn't find thread %ld\n", thread);
		send_error();
		return;
	}
	trace_mode = True;
	access_nr = 0;
	do {
		run_thread(rt, &cer, False);
	} while (cer.type == EVENT_footstep ||
		 cer.type == EVENT_load ||
		 cer.type == EVENT_store);
	trace_mode = False;
	send_okay();
}

static void
do_thread_state_command(void)
{
	struct replay_thread *rt;
	char buf[128];
	for (rt = head_thread; rt; rt = rt->next) {
		VG_(sprintf)((Char *)buf, "%d: dead %d, last record %d",
			     rt->id, rt->dead, rt->last_record_nr);
		send_string(VG_(strlen)((Char *)buf), buf);
	}
	send_okay();
}

static char *
my_vasprintf(const char *fmt, va_list args)
{
	char *buffer;
	unsigned buffer_size;
	va_list a;
	UInt res;

	buffer_size = 128;
	while (1) {
		buffer = VG_(malloc)("vasprintf", buffer_size);
		va_copy(a, args);
		res = VG_(vsnprintf)((Char *)buffer, buffer_size, fmt,
				     a);
		va_end(a);
		if (res < buffer_size && res != 0)
			return buffer;
		VG_(free)(buffer);
		buffer_size *= 2;
	}
}

static struct failure_reason *
reason_control(void)
{
	struct failure_reason *fr;
	fr = VG_(malloc)("reason_control", sizeof(*fr));
	VG_(memset)(fr, 0, sizeof(*fr));
	fr->reason = REASON_CONTROL;
	return fr;
}

static struct failure_reason *
reason_data(struct expression *e1, struct expression *e2)
{
	struct failure_reason *fr;
	fr = VG_(malloc)("reason_data", sizeof(*fr));
	VG_(memset)(fr, 0, sizeof(*fr));
	fr->reason = REASON_DATA;
	fr->arg1 = e1;
	fr->arg2 = e2;
	return fr;
}

static struct failure_reason *
reason_other(void)
{
	struct failure_reason *fr;
	fr = VG_(malloc)("reason_other", sizeof(*fr));
	VG_(memset)(fr, 0, sizeof(*fr));
	fr->reason = REASON_OTHER;
	return fr;
}

static void
replay_failed(struct failure_reason *failure_reason, const char *fmt, ...)
{
	va_list args;
	struct control_command cmd;
	char *msg;

	va_start(args, fmt);
	msg = my_vasprintf(fmt, args);
	va_end(args);

	VG_(printf)("FAILED %s\n", msg);

	send_error();
	while (1) {
		get_control_command(&cmd);
		switch (cmd.cmd) {
		case WORKER_SNAPSHOT:
			control_process_socket = do_snapshot(control_process_socket);
			break;
		case WORKER_KILL:
			send_okay();
			my__exit(0);
		case WORKER_TRACE_THREAD:
			do_trace_thread_command(cmd.u.trace_thread.thread);
			break;
		case WORKER_THREAD_STATE:
			do_thread_state_command();
			break;
		case WORKER_REPLAY_STATE:
			send_ancillary(ANCILLARY_REPLAY_FAILED, failure_reason->reason);
			if (failure_reason->arg1)
				send_expression(failure_reason->arg1);
			if (failure_reason->arg2)
				send_expression(failure_reason->arg2);
			send_string(VG_(strlen)((Char *)msg), msg);
			send_okay();
			break;
		default:
			VG_(printf)("Only the kill, trace thread, and snapshot commands are valid after replay fails (got %x)\n",
				cmd.cmd);
			send_error();
			break;
		}
	}
}

#define replay_assert_eq(reason, a, b)					\
	do {								\
		if ((a) != (b)) {					\
			replay_failed(reason,				\
				      "%d: Replay failed at %d: %s(%lx) != %s(%lx)\n", \
				      record_nr,			\
				      __LINE__,				\
				      #a,				\
				      (unsigned long)(a),		\
				      #b,				\
				      (unsigned long)(b));		\
		}							\
	} while (0)


static void
validate_event(const struct record_header *rec,
	       const struct client_event_record *event)
{
	const void *payload = rec + 1;
	const unsigned long *args = event->args;

	switch (event->type) {
	case EVENT_footstep: {
		const struct footstep_record *fr = payload;
		replay_assert_eq(reason_control(), rec->cls, RECORD_footstep);
		replay_assert_eq(reason_control(), fr->rip, args[0]);
		replay_assert_eq(reason_data(expr_reg(REG_RDX),
					     expr_const(fr->rdx)),
				 fr->rdx, args[1]);
		replay_assert_eq(reason_data(expr_reg(REG_RCX),
					     expr_const(fr->rcx)),
				 fr->rcx, args[2]);
		replay_assert_eq(reason_data(expr_reg(REG_RAX),
					     expr_const(fr->rax)),
				 fr->rax, args[3]);
		return;
	}
	case EVENT_syscall: {
		const struct syscall_record *sr = payload;
		replay_assert_eq(reason_control(), rec->cls, RECORD_syscall);
		replay_assert_eq(reason_data(expr_reg(REG_RAX),
					     expr_const(sr->syscall_nr)),
				 sr->syscall_nr, args[0]);
		replay_assert_eq(reason_data(expr_reg(REG_RDI),
					     expr_const(sr->arg1)),
				 sr->arg1, args[1]);
		replay_assert_eq(reason_data(expr_reg(REG_RSI),
					     expr_const(sr->arg2)),
				 sr->arg2, args[2]);
		replay_assert_eq(reason_data(expr_reg(REG_RDX),
					     expr_const(sr->arg3)),
				 sr->arg3, args[3]);
		return;
	}
	case EVENT_rdtsc: {
		replay_assert_eq(reason_control(), rec->cls, RECORD_rdtsc);
		return;
	}
	case EVENT_load: {
		const struct mem_read_record *mrr = payload;
		const void *mp = mrr + 1;
		replay_assert_eq(reason_control(), rec->cls, RECORD_mem_read);
		replay_assert_eq(reason_other(), mrr->ptr, (void *)args[0]);
		replay_assert_eq(reason_control(),
				 rec->size - sizeof(*rec) - sizeof(*mrr),
				 args[1]);
		switch (args[1]) {
		case 1:
			replay_assert_eq(reason_data(expr_mem1(mrr->ptr),
						     expr_const(*(unsigned char *)mp)),
					 *(unsigned char *)mp,
					 *(unsigned char *)args[2]);
			break;
		case 2:
			replay_assert_eq(reason_data(expr_mem2(mrr->ptr),
						     expr_const(*(unsigned short *)mp)),
					 *(unsigned short *)mp,
					 *(unsigned short *)args[2]);
			break;
		case 4:
			replay_assert_eq(reason_data(expr_mem4(mrr->ptr),
						     expr_const(*(unsigned *)mp)),
					 *(unsigned *)mp,
					 *(unsigned *)args[2]);
			break;
		case 8:
			replay_assert_eq(reason_data(expr_mem8(mrr->ptr),
						     expr_const(*(unsigned long *)mp)),
					 *(unsigned long *)mp,
					 *(unsigned long *)args[2]);
			break;
		case 16:
			replay_assert_eq(reason_data(expr_mem8(mrr->ptr),
						     expr_const(((unsigned long *)mp)[0])),
					 ((unsigned long *)mp)[0],
					 ((unsigned long *)args[2])[0]);
			replay_assert_eq(reason_data(expr_mem8(mrr->ptr + 1),
						     expr_const(((unsigned long *)mp)[1])),
					 ((unsigned long *)mp)[1],
					 ((unsigned long *)args[2])[1]);
			break;
		default:
			ASSUME(0);
		}
		return;
	}
	case EVENT_store: {
		const struct mem_read_record *mwr = payload;
		replay_assert_eq(reason_control(), rec->cls, RECORD_mem_write);
		replay_assert_eq(reason_other(), mwr->ptr, (void *)args[0]);
		replay_assert_eq(reason_control(),
				 rec->size - sizeof(*rec) - sizeof(*mwr),
				 args[1]);
		switch (args[1]) {
		case 1:
			replay_assert_eq(reason_other(),
					 *(unsigned char *)(mwr + 1),
					 *(unsigned char *)args[2]);
			break;
		case 2:
			replay_assert_eq(reason_other(),
					 *(unsigned short *)(mwr + 1),
					 *(unsigned short *)args[2]);
			break;
		case 4:
			replay_assert_eq(reason_other(),
					 *(unsigned *)(mwr + 1),
					 *(unsigned *)args[2]);
			break;
		case 8:
			replay_assert_eq(reason_other(),
					 *(unsigned long *)(mwr + 1),
					 *(unsigned long *)args[2]);
			break;
		case 16:
			replay_assert_eq(reason_other(),
					 ((unsigned long *)(mwr + 1))[0],
					 ((unsigned long *)args[2])[0]);
			replay_assert_eq(reason_other(),
					 ((unsigned long *)(mwr + 1))[1],
					 ((unsigned long *)args[2])[1]);
			break;
		default:
			ASSUME(0);
		}
		return;
	}
	case EVENT_client_request: {
		const struct client_req_record *crr = payload;
		replay_assert_eq(reason_control(), rec->cls, RECORD_client);
		replay_assert_eq(reason_control(), args[0], crr->flavour);
		return;
	}
	case EVENT_resched_candidate:
		/* Should have been handled by caller. */
		VG_(tool_panic)((Char *)"resched candidate in bad place");
	case EVENT_nothing:
		VG_(tool_panic)((Char *)"validate event when no event present?");
	}
	VG_(tool_panic)((Char *)"bad event type");
}

static jmp_buf
replay_memory_jmpbuf;

static void
replay_memory_sighandler(Int signo, Addr addr)
{
	if (signo == VKI_SIGBUS || signo == VKI_SIGSEGV) {
		/* Something bad has happened, and we can't replay the
		   memory record which we captured.  This shouldn't
		   happen if we follow the script, but it's possible
		   if we've diverged. */
		__builtin_longjmp(replay_memory_jmpbuf, 1);
	}
}

static void
replay_memory_record(struct record_header *rh,
		     struct memory_record *mr)
{
	vki_sigset_t sigmask;
	Bool should_be_in_gen;

	should_be_in_gen = VG_(in_generated_code);
	if (__builtin_setjmp(&replay_memory_jmpbuf)) {
		VG_(in_generated_code) = should_be_in_gen;
		VG_(set_fault_catcher)(NULL);
		VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
		VG_(printf)("Signal trying to replay memory at %p -> thread failed\n",
			    mr->ptr);
		my__exit(1);
	}

	VG_(in_generated_code) = False;
	VG_(sigprocmask)(VKI_SIG_SETMASK, NULL, &sigmask);
	VG_(set_fault_catcher)(replay_memory_sighandler);
	VG_(memcpy)(mr->ptr,
		    mr + 1,
		    rh->size - sizeof(*rh) - sizeof(*mr));
	VG_(set_fault_catcher)(NULL);
	VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
	VG_(in_generated_code) = should_be_in_gen;
}

static void
process_memory_records(struct record_consumer *logfile)
{
	struct record_header *rh;

	rh = get_current_record(logfile);
	while (rh && rh->cls == RECORD_memory) {
		replay_memory_record(rh, (struct memory_record *)(rh + 1));
		finish_this_record(logfile);
		rh = get_current_record(logfile);
	}
}

/* This finishes the current record */
static void
replay_syscall(const struct syscall_record *sr,
	       struct replay_thread *rt,
	       struct client_event_record *event,
	       struct record_consumer *logfile)
{
	VexGuestAMD64State *state = (VexGuestAMD64State *)event->args[4];

	switch (event->args[0]) {
		/* Very easy syscalls: don't bother running them, and
		   just drop in the recorded return value. */
	case __NR_access:
	case __NR_close:
	case __NR_fstat:
	case __NR_getcwd:
	case __NR_getuid:
	case __NR_open:
	case __NR_read:
	case __NR_stat:
	case __NR_uname:
	case __NR_getrlimit:

	case __NR_futex: /* XXX not even slightly right */

		state->guest_RAX = sysres_to_eax(sr->syscall_res);
		finish_this_record(logfile);
		break;

	case __NR_exit:
		rt->dead = True;
		finish_this_record(logfile);
		break;

		/* Moderately easy syscalls: run them and assert that
		   the result is the same. */
	case __NR_arch_prctl:
	case __NR_brk:
	case __NR_mprotect:
	case __NR_munmap:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:
	case __NR_set_robust_list:
		VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);
		tl_assert(sysres_to_eax(sr->syscall_res) == state->guest_RAX);
		finish_this_record(logfile);
		break;

	case __NR_set_tid_address:
		if (!sr_isError(sr->syscall_res))
			VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);
		state->guest_RAX = sysres_to_eax(sr->syscall_res);;
		finish_this_record(logfile);
		break;

	case __NR_exit_group:
		VG_(printf)("%d: Exit group, status %ld.\n", record_nr, event->args[1]);
		finish_this_record(logfile);
		break;

	case __NR_mmap: {
		Addr addr;
		ULong length;
		SysRes map_res;
		Word prot;

		if (sr_isError(sr->syscall_res)) {
			state->guest_RAX = sysres_to_eax(sr->syscall_res);
			break;
		}
		addr = sr_Res(sr->syscall_res);
		length = event->args[2];
		prot = event->args[3];
		map_res = VG_(am_mmap_anon_fixed_client)(addr,
							 length,
							 prot | VKI_PROT_WRITE);
		tl_assert(!sr_isError(map_res));

		finish_this_record(logfile);

		process_memory_records(logfile);
		if (!(prot & VKI_PROT_WRITE))
			my_mprotect((void *)addr, length, prot);
		state->guest_RAX = addr;
		break;
	}

	case __NR_clone:
		/* Because of the way we turn syscall exits into calls
		   to syscall_event(), the rip points to the start of
		   the syscall instruction rather than the end.
		   That's fine in the parent thread, because we'll
		   finish the IRSB and advance it immediately, but
		   it's no good in the child, which will immediately
		   issue another clone system call and set off a fork
		   bomb.  Fix it up by just manually bumping RIP. */
		state->guest_RIP += 2;

		/* Try to issue the syscall.  This gets caught in
		   replay_clone_syscall() and turned into a coroutine
		   create. */
		if (!sr_isError(sr->syscall_res))
			VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);

		state->guest_RAX = sysres_to_eax(sr->syscall_res);
		finish_this_record(logfile);
		break;

	default:
		VG_(printf)("Don't yet support syscall %lld\n",
			    state->guest_RAX);
		ASSUME(0);
	}

	process_memory_records(logfile);
}

/* This finishes the current record */
static void
replay_record(const struct record_header *rec, struct replay_thread *thr,
	      struct client_event_record *event, struct record_consumer *logfile)
{
	const void *payload = rec + 1;
	switch (rec->cls) {
	case RECORD_rdtsc: {
		const struct rdtsc_record *rr = payload;
		thr->rdtsc_result = rr->stashed_tsc;
		finish_this_record(logfile);
		break;
	}
	case RECORD_syscall: {
		const struct syscall_record *sr = payload;
		replay_syscall(sr, thr, event, logfile);
		break;
	}
	default:
		finish_this_record(logfile);
		break;
	}
}

static void
run_for_n_mem_accesses(struct replay_thread *thr,
		       unsigned nr_accesses)
{
	struct client_event_record cer;

	trace_mode = True;
	access_nr = 0;
	while (access_nr < nr_accesses) {
		run_thread(thr, &cer, False);
		if (cer.type == EVENT_footstep)
			continue;
		if (cer.type != EVENT_load &&
		    cer.type != EVENT_store) {
			replay_failed(reason_other(),
				      "%d: Client made unexpected event %x\n",
				      record_nr,
				      cer.type);
		}
	}
	trace_mode = False;
}

static void
run_for_n_records(struct record_consumer *logfile,
		  unsigned nr_records,
		  Bool trace_control)
{
	const struct record_header *rec;
	struct replay_thread *thr;
	struct client_event_record thread_event;

	while (record_nr != nr_records) {
		rec = get_current_record(logfile);
		if (!rec)
			break;
		if (rec->cls == RECORD_new_thread ||
		    rec->cls == RECORD_thread_blocking ||
		    rec->cls == RECORD_thread_unblocked ||
		    (!use_footsteps &&
		     rec->cls == RECORD_footstep) ||
		    (!use_memory &&
		     (rec->cls == RECORD_mem_read ||
		      rec->cls == RECORD_mem_write))) {
			finish_this_record(logfile);
			continue;
		}

		record_nr++;
		access_nr = 0;

		tl_assert(rec->cls != RECORD_memory);

		thr = get_thread_by_id(rec->tid);
		tl_assert(thr != NULL);

		do {
			run_thread(thr, &thread_event, trace_control);
		} while (!(use_memory ||
			   (thread_event.type != EVENT_load &&
			    thread_event.type != EVENT_store)));


		ASSUME(thread_event.type != EVENT_resched_candidate);

		validate_event(rec, &thread_event);

		replay_record(rec, thr, &thread_event, logfile); /* Finishes the record */

		thr->last_record_nr = record_nr;
	}
}

static void
init_register(struct abstract_interpret_value *aiv,
	      unsigned long value)
{
	aiv->v1 = value;
	aiv->v2 = 0;
	free_expression(aiv->origin);
	aiv->origin = expr_imported();
}

static void
init_register_xmm(struct abstract_interpret_value *aiv,
		  const U128 *v)
{
	VG_(memcpy)(&aiv->v1, v, 16);
	free_expression(aiv->origin);
	free_expression(aiv->origin2);
	aiv->origin = expr_imported();
	aiv->origin2 = expr_imported();
}

static void
initialise_is_for_vex_state(struct interpret_state *is,
			    const VexGuestArchState *state)
{
	init_register(&is->rax, state->guest_RAX);
	init_register(&is->rcx, state->guest_RCX);
	init_register(&is->rdx, state->guest_RDX);
	init_register(&is->rbx, state->guest_RBX);
	init_register(&is->rsp, state->guest_RSP);
	init_register(&is->rbp, state->guest_RBP);
	init_register(&is->rdi, state->guest_RDI);
	init_register(&is->rsi, state->guest_RSI);
	init_register(&is->r8, state->guest_R8);
	init_register(&is->r9, state->guest_R9);
	init_register(&is->r10, state->guest_R10);
	init_register(&is->r11, state->guest_R11);
	init_register(&is->r12, state->guest_R12);
	init_register(&is->r13, state->guest_R13);
	init_register(&is->r14, state->guest_R14);
	init_register(&is->r15, state->guest_R15);
	init_register(&is->rip, state->guest_RIP);

	init_register(&is->cc_op, state->guest_CC_OP);
	init_register(&is->cc_dep1, state->guest_CC_DEP1);
	init_register(&is->cc_dep2, state->guest_CC_DEP2);
	init_register(&is->cc_ndep, state->guest_CC_NDEP);

	init_register(&is->d_flag, state->guest_DFLAG);
	init_register(&is->fs_zero, state->guest_FS_ZERO);

	init_register_xmm(&is->xmm0, &state->guest_XMM0);
	init_register_xmm(&is->xmm1, &state->guest_XMM1);
}

static void
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
	free_expression(aiv->origin);
	aiv->origin = NULL;
	return aiv->v1;
}

static void
commit_register_xmm(U128 *r, struct abstract_interpret_value *aiv)
{
	free_expression(aiv->origin);
	aiv->origin = NULL;
	VG_(memcpy)(r, &aiv->v1, 16);
}

static void
commit_is_to_vex_state(struct interpret_state *is,
		       VexGuestArchState *state)
{
	state->guest_RAX = commit_register(&is->rax);
	state->guest_RCX = commit_register(&is->rcx);
	state->guest_RDX = commit_register(&is->rdx);
	state->guest_RBX = commit_register(&is->rbx);
	state->guest_RSP = commit_register(&is->rsp);
	state->guest_RBP = commit_register(&is->rbp);
	state->guest_RSI = commit_register(&is->rsi);
	state->guest_RDI = commit_register(&is->rdi);
	state->guest_R8 = commit_register(&is->r8);
	state->guest_R9 = commit_register(&is->r9);
	state->guest_R10 = commit_register(&is->r10);
	state->guest_R11 = commit_register(&is->r11);
	state->guest_R12 = commit_register(&is->r12);
	state->guest_R13 = commit_register(&is->r13);
	state->guest_R14 = commit_register(&is->r14);
	state->guest_R15 = commit_register(&is->r15);
	state->guest_RIP = commit_register(&is->rip);

	state->guest_CC_OP = commit_register(&is->cc_op);
	state->guest_CC_DEP1 = commit_register(&is->cc_dep1);
	state->guest_CC_DEP2 = commit_register(&is->cc_dep2);
	state->guest_CC_NDEP = commit_register(&is->cc_ndep);

	state->guest_DFLAG = commit_register(&is->d_flag);
	state->guest_FS_ZERO = commit_register(&is->fs_zero);

	commit_register_xmm(&state->guest_XMM0, &is->xmm0);
	commit_register_xmm(&state->guest_XMM1, &is->xmm1);
}

static void
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
	VG_(printf)("Committing interpreter memory...\n");
	for (iml = head_interpret_mem_lookaside;
	     iml != NULL;
	     iml = next) {
		next = iml->next;
		free_expression(iml->aiv.origin);
		VG_(free)(iml);
	}
	head_interpret_mem_lookaside = NULL;
	VG_(printf)("Done commit.\n");
}

static void
run_control_command(struct control_command *cmd, struct record_consumer *logfile)
{
	struct replay_thread *rt;

	logfile_reset_file_ptr(logfile);
	switch (cmd->cmd) {
	case WORKER_KILL:
		send_okay();
		my__exit(0);
	case WORKER_RUN:
		run_for_n_records(logfile, cmd->u.run.nr, False);
		send_okay();
		break;
	case WORKER_TRACE:
		trace_mode = True;
		run_for_n_records(logfile, cmd->u.trace.nr, False);
		trace_mode = False;
		send_okay();
		break;
	case WORKER_CONTROL_TRACE:
		initialise_interpreter_state();
		run_for_n_records(logfile, cmd->u.control_trace.nr, True);
		commit_interpreter_state();
		send_okay();
		break;
	case WORKER_RUNM:
		rt = get_thread_by_id(cmd->u.runm.thread);
		if (!rt) {
			VG_(printf)("Cannot find thread %ld\n", cmd->u.runm.thread);
			send_error();
		} else {
			run_for_n_mem_accesses(rt, cmd->u.runm.nr);
			send_okay();
		}
		break;
	case WORKER_SNAPSHOT:
		control_process_socket = do_snapshot(control_process_socket);
		break;
	case WORKER_TRACE_THREAD:
		do_trace_thread_command(cmd->u.trace_thread.thread);
		break;
	case WORKER_TRACE_ADDRESS:
		trace_address = cmd->u.trace_mem.address;
		run_for_n_records(logfile, -1, False);
		send_okay();
		break;
	case WORKER_THREAD_STATE:
		do_thread_state_command();
		break;
	case WORKER_REPLAY_STATE:
		send_ancillary(ANCILLARY_REPLAY_SUCCESS);
		send_okay();
		break;
	default:
		VG_(tool_panic)((Char *)"Bad worker command");
	}
}

/* The replay machine itself.  This consumes records from the log file
   and decides how we're going to try to satisfy them. */
static void
replay_machine_fn(void)
{
	struct record_consumer logfile;
	struct control_command cmd;

	open_logfile(&logfile, (Char *)"logfile1");

	while (1) {
		get_control_command(&cmd);
		run_control_command(&cmd, &logfile);
	}

	my__exit(0);
}

static void
init(void)
{
	control_process_socket = ui_loop();

	head_thread = VG_(malloc)("head thread", sizeof(*head_thread));
	VG_(memset)(head_thread, 0, sizeof(*head_thread));
	head_thread->id = 1;
	initialise_coroutine(&head_thread->coroutine, "head thread");

	run_coroutine(&head_thread->coroutine, &replay_machine,
		      "start of day");

	VG_(running_tid) = VG_INVALID_THREADID;
}


/* Thread creation machinery. */
static Bool
creating_new_thread;
static struct coroutine
creating_thread_coroutine;
static struct replay_thread *
newly_spawning_thread;

static void
new_thread_starting(void)
{
	if (!creating_new_thread)
		return;

	newly_spawning_thread->id = VG_(running_tid);
	newly_spawning_thread->next = head_thread;
	head_thread = newly_spawning_thread;

	run_coroutine(&newly_spawning_thread->coroutine,
		      &creating_thread_coroutine,
		      "new_thread_starting");
}

/* We tweak Valgrind to call this rather than the normal sys_clone()
   system call when it wants to create threads.  That allows us to
   take control over scheduling and so forth. */
static Long
replay_clone_syscall(Word (*fn)(void *),
		     void *stack,
		     Long flags,
		     void *arg,
		     Long *child_tid,
		     Long *parent_tid,
		     vki_modify_ldt_t *modify_ldt)
{
	tl_assert(VG_(running_tid) == VG_INVALID_THREADID);
	tl_assert(!creating_new_thread);
	creating_new_thread = True;

	initialise_coroutine(&creating_thread_coroutine, "creating thread coroutine");

	newly_spawning_thread = VG_(malloc)("child thread",
					    sizeof(struct replay_thread));
	VG_(memset)(newly_spawning_thread, 0, sizeof(struct replay_thread));
	make_coroutine(&newly_spawning_thread->coroutine,
		       "child client thread",
		       stack,
		       0,
		       fn,
		       1,
		       arg);

	/* Get it going. */
	run_coroutine(&creating_thread_coroutine,
		      &newly_spawning_thread->coroutine,
		      "create new thread");

	VG_(running_tid) = VG_INVALID_THREADID;

	tl_assert(creating_new_thread);
	creating_new_thread = False;

	return 0xaabbccdd;
}

static void
fini(Int ignore)
{
	VG_(printf)("Huh? Didn't expect fini() to get called.\n");
}

static Bool
process_cmd_line(Char *argv)
{
	if (!VG_(strcmp)(argv, (Char *)"--use-footsteps")) {
		use_footsteps = True;
		return True;
	}
	if (!VG_(strcmp)(argv, (Char *)"--use-memory")) {
		use_memory = True;
		return True;
	}
        return False;
}

static void
print_usage(void)
{
}

static void
print_debug(void)
{
}

static void
pre_clo_init(void)
{
	static unsigned char replay_machine_stack[16384];
	make_coroutine(&replay_machine,
		       "replay machine",
		       replay_machine_stack,
		       sizeof(replay_machine_stack),
		       replay_machine_fn,
		       0);

	VG_(tool_handles_synchronisation) = True;
	tool_provided_rdtsc = rdtsc_event;
	VG_(tool_provided_thread_starting) = new_thread_starting;
	tool_provided_clone_syscall =
		replay_clone_syscall;

	VG_(details_name)((signed char *)"ppres_rep");
	VG_(details_version)((signed char *)"0.0");
	VG_(details_copyright_author)((signed char *)"Steven Smith");
	VG_(details_bug_reports_to)((signed char *)"sos22@cam.ac.uk");
	VG_(details_description)((signed char *)"Replayer for PPRES");
	VG_(basic_tool_funcs)(init, instrument_func, fini);
	VG_(needs_client_requests)(client_request_event);
	VG_(needs_command_line_options)(process_cmd_line,
					print_usage,
					print_debug);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
