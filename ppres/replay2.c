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

#define NOISY_AFTER_RECORD 210500

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
	unsigned long v;
	const struct expression *origin;
};

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
};

struct interpret_state {
	struct expression_result *temporaries;

	/* Update commit_is_to_vex_state, initialise_is_for_vex_state,
	   get_aiv_for_offset, and gc_explore_interpret_state when
	   changing these. */
	struct abstract_interpret_value gregs[16];
	struct abstract_interpret_value rip;

	struct abstract_interpret_value cc_op;
	struct abstract_interpret_value cc_dep1;
	struct abstract_interpret_value cc_dep2;
	struct abstract_interpret_value cc_ndep;

	struct abstract_interpret_value d_flag;
	struct abstract_interpret_value fs_zero;

	struct abstract_interpret_value xmm[32];
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
		struct {
			unsigned long val;
			struct expression *next, *prev;
		} cnst;
		struct {
			const void *ptr;
			unsigned size;
		} mem;
		struct {
			const struct expression *arg1;
			const struct expression *arg2;
		} binop;
		struct {
			const struct expression *e;
		} unop;
	} u;
};

struct failure_reason {
	unsigned reason;
	const struct expression *arg1;
	const struct expression *arg2;
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

static void footstep_event(Addr rip, Word rdx, Word rcx, Word rax,
			   unsigned long xmm3a, unsigned long xmm0a);
static void store_event(void *ptr, unsigned size, const void *written_bytes,
			unsigned long rsp);
static IRSB *instrument_func(VgCallbackClosure *closure,
			     IRSB *sb_in,
			     VexGuestLayout *layout,
			     VexGuestExtents *vge,
			     IRType gWordTy,
			     IRType hWordTy);

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
}

static const struct expression *
copy_expression(const struct expression *e)
{
	return e;
}

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

	if (op_binop(e->type)) {
		gc_explore_expression(e->u.binop.arg1);
		gc_explore_expression(e->u.binop.arg2);
		return;
	} else {
		switch (e->type) {
		case EXPR_CONST:
		case EXPR_REG:
		case EXPR_IMPORTED:
		case EXPR_MEM:
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

	tl_assert(is->temporaries == NULL);
	for (x = 0; x < 16; x++)
		gc_explore_aiv(&is->gregs[x]);

	gc_explore_aiv(&is->rip);

	gc_explore_aiv(&is->cc_op);
	gc_explore_aiv(&is->cc_dep1);
	gc_explore_aiv(&is->cc_dep2);
	gc_explore_aiv(&is->cc_ndep);
	gc_explore_aiv(&is->d_flag);
	gc_explore_aiv(&is->fs_zero);
	for (x = 0; x < 16; x++)
		gc_explore_aiv(&is->xmm[x]);
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

static void
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
	for (rt = head_thread; rt; rt = rt->next)
		gc_explore_interpret_state(&rt->interpret_state);
	gc_explore_mem_lookaside();

	/* Go back and rebuild the free lists. */
	head_free_expression = NULL;
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
	return work;
}

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

static const struct expression *
expr_reg(unsigned reg)
{
	struct expression *e;
	e = _new_expression(EXPR_REG);
	e->u.reg = reg;
	return e;
}

static const struct expression *
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

static const struct expression *
expr_mem(void *ptr, unsigned size)
{
	struct expression *e;
	e = _new_expression(EXPR_MEM);
	e->u.mem.size = size;
	e->u.mem.ptr = ptr;
	return e;
}

#define expr_mem1(p) expr_mem((p), 1)
#define expr_mem2(p) expr_mem((p), 2)
#define expr_mem4(p) expr_mem((p), 4)
#define expr_mem8(p) expr_mem((p), 8)

static const struct expression *
expr_not(const struct expression *e)
{
	struct expression *r;
	r = _new_expression(EXPR_NOT);
	r->u.unop.e = e;
	return r;
}

static const struct expression *
expr_imported(void)
{
	return _new_expression(EXPR_IMPORTED);
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

static const struct expression *
expr_binop(const struct expression *e1, const struct expression *e2, unsigned op)
{
	struct expression *e;
	const struct expression *ec;

	if (e1->type == EXPR_CONST && e2->type == EXPR_CONST) {
		/* Try to do some constant folding.  We only do this
		   for a few special cases. */
		ec = NULL;
		switch (op) {
		case EXPR_ADD:
			ec = expr_const(e1->u.cnst.val + e2->u.cnst.val);
			break;
		default:
			break;
		}
		if (ec) {
			free_expression(e1);
			free_expression(e2);
			return ec;
		}
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

	if (binop_lident_0(op) &&
	    e1->type == EXPR_CONST &&
	    e1->u.cnst.val == 0) {
		free_expression(e1);
		return e2;
	}
	if (binop_rident_0(op) &&
	    e2->type == EXPR_CONST &&
	    e2->u.cnst.val == 0) {
		free_expression(e2);
		return e1;
	}
	e = _new_expression(op);
	e->u.binop.arg1 = e1;
	e->u.binop.arg2 = e2;
	return e;
}

#define mk_expr(name1, name2)						\
	static inline const struct expression *				\
	expr_ ## name1 (const struct expression *e1,			\
			const struct expression *e2)			\
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
send_expression(const struct expression *e)
{
#warning WRITE ME
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
	if (offset < 16 * 8) {
		tl_assert(!(offset % 8));
		return &state->gregs[offset / 8];
	} else if (offset >= 200 && (offset - 200) < 32 * 8) {
		offset -= 200;
		tl_assert(!(offset % 8));
		return &state->xmm[offset / 8];
	}

	switch (offset) {
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
	*dest = *src;
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
interpreter_do_load(struct expression_result *er,
		    unsigned size,
		    unsigned long addr)
{
	VG_(memset)(er, 0, sizeof(*er));
	if (size > 8) {
		tl_assert(size == 16);
		er->hi.origin = find_origin_expression(head_interpret_mem_lookaside,
						       8,
						       addr + 8);
		VG_(memcpy)(&er->hi.v, (const void *)addr + 8, 8);
		size = 8;
	} else {
		er->hi.origin = NULL;
	}
	VG_(memcpy)(&er->lo.v, (const void *)addr, size);
	er->lo.origin = find_origin_expression(head_interpret_mem_lookaside,
					       size,
					       addr);
}

static void
eval_expression(struct interpret_state *state,
		struct expression_result *dest,
		IRExpr *expr);

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
	tl_assert(condcode.lo.origin->type == EXPR_CONST);

	eval_expression(state, &op, args[1]);
	tl_assert(op.lo.origin->type == EXPR_CONST);

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
			dest->lo.origin = dep1.lo.origin;
			break;
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v == dep2.lo.v;
			dest->lo.origin = expr_eq(dep1.lo.origin,
						  dep2.lo.origin);
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
		case AMD64G_CC_OP_ADDB:
		case AMD64G_CC_OP_ADDW:
		case AMD64G_CC_OP_ADDL:
		case AMD64G_CC_OP_ADDQ:
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
			free_expression(dest->lo.origin);
			dest->lo.origin =
				expr_be(expr_and(expr_add(copy_expression(dep1.lo.origin),
							  expr_const(0x80)),
						 expr_const(0xff)),
					expr_and(expr_add(copy_expression(dep2.lo.origin),
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
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_le(copy_expression(dep1.lo.origin),
					       copy_expression(dep2.lo.origin));
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
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_b(copy_expression(dep1.lo.origin),
					      copy_expression(dep2.lo.origin));
			break;
		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = dep1.lo.v + dep2.lo.v < dep1.lo.v;
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_b(expr_add(copy_expression(dep1.lo.origin),
						       copy_expression(dep2.lo.origin)),
					      copy_expression(dep1.lo.origin));
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
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_be(copy_expression(dep1.lo.origin),
					       copy_expression(dep2.lo.origin));
			break;
		default:
			VG_(printf)("Strange operation code %ld for be\n", op.lo.v);
			VG_(tool_panic)((Char *)"failed");
		}
		break;

	case AMD64CondS:
		switch (op.lo.v) {
		case AMD64G_CC_OP_LOGICL:
			dest->lo.v = dep1.lo.v >> 31;
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_shrl(copy_expression(dep1.lo.origin),
						 expr_const(31));
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = dep1.lo.v >> 63;
			free_expression(dest->lo.origin);
			dest->lo.origin = expr_shrl(copy_expression(dep1.lo.origin),
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
	free_expression(dep1.lo.origin);
	free_expression(dep2.lo.origin);
	free_expression(ndep.lo.origin);

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
	tl_assert(op.lo.origin->type == EXPR_CONST);
	free_expression(op.lo.origin);

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
		free_expression(dest->lo.origin);
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
		free_expression(dest->lo.origin);
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

	free_expression(dep1.lo.origin);
	free_expression(dep2.lo.origin);
	free_expression(ndep.lo.origin);
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

static void load_event(const void *ptr, unsigned size, void *read_bytes,
		       unsigned long rsp);
static void
eval_expression(struct interpret_state *state,
		struct expression_result *dest,
		IRExpr *expr)
{
#define ORIGIN(x)				\
	do {					\
		const struct expression *t;	\
		t = dest->lo.origin;		\
		dest->lo.origin = x;		\
		free_expression(t);		\
	} while (0)

	tl_assert(expr != NULL);
	dest->lo.v = 0xdeadbeeff001f001;
	dest->lo.origin = NULL;
	dest->hi.v = 0xaaaaaaaaaaaaaaaa;
	dest->hi.origin = NULL;

	switch (expr->tag) {
	case Iex_Get: {
		struct abstract_interpret_value *src;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src = get_aiv_for_offset(state,
					 expr->Iex.Get.offset - sub_word_offset);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
			tl_assert(!sub_word_offset);
			copy_aiv(&dest->lo, src);
			break;
		case Ity_V128:
			tl_assert(!sub_word_offset);
			copy_aiv(&dest->lo, src);
			copy_aiv(&dest->hi,
				 get_aiv_for_offset(state, expr->Iex.Get.offset + 8));
			break;
		case Ity_I32:
			tl_assert(!(sub_word_offset % 4));
			dest->lo.v = (src->v >> (sub_word_offset * 8)) & 0xffffffff;
			dest->lo.origin = expr_and(expr_const(0xffffffff),
						   expr_shrl(src->origin,
							     expr_const(sub_word_offset * 8)));
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->lo.v = (src->v >> (sub_word_offset * 8)) & 0xffff;
			dest->lo.origin = expr_and(expr_const(0xffff),
						   expr_shrl(src->origin,
							     expr_const(sub_word_offset * 8)));
			break;
		case Ity_I8:
			dest->lo.v = (src->v >> (sub_word_offset * 8)) & 0xff;
			dest->lo.origin = expr_and(expr_const(0xff),
						   expr_shrl(src->origin,
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
			VG_(printf)("Add64x %lx:%lx + %lx:%lx -> %lx:%lx\n",
				    arg1.lo.v, arg1.hi.v, arg2.lo.v, arg2.hi.v,
				    dest->lo.v, dest->hi.v);
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
			dest->lo.v = (long)arg1.lo.v <= (long)arg2.lo.v;
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
			VG_(printf)("%lx:%lx * %lx:%lx -> %lx\n", arg1.lo.v,
				    arg1.hi.v, arg2.lo.v, arg2.hi.v, dest->lo.v);
			dest->lo.origin = expr_mul(arg1.lo.origin, arg2.lo.origin);
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
			VG_(printf)("Interleave hi 64x2 %lx %lx -> %lx:%lx\n",
				    arg2.hi.v, arg1.hi.v, dest->hi.v, dest->lo.v);
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
			VG_(printf)("Interleave lo32x4 %lx:%lx %lx:%lx -> %lx:%lx\n",
				    arg1.hi.v, arg1.lo.v, arg2.hi.v, arg2.lo.v,
				    dest->hi.v, dest->lo.v);
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
			VG_(printf)("Interleave hi32x4 %lx:%lx %lx:%lx -> %lx:%lx\n",
				    arg1.hi.v, arg1.lo.v, arg2.hi.v, arg2.lo.v,
				    dest->hi.v, dest->lo.v);
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
			VG_(printf)("shln64x2 %lx:%lx %lx:%lx -> %lx:%lx\n",
				    arg1.lo.v, arg1.hi.v, arg2.lo.v, arg2.hi.v,
				    dest->lo.v, dest->hi.v);
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
			VG_(printf)("%lx:%lx > %lx:%lx -> %lx:%lx\n",
				    arg1.lo.v, arg1.hi.v, arg2.lo.v, arg2.hi.v,
				    dest->lo.v, dest->hi.v);
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
		case Iop_8Sto32:
			dest->lo.v = (int)(signed char)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(56)),
					 expr_const(56)));
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

static void commit_interpreter_state(void);
static void initialise_interpreter_state(void);

static struct expression_result
do_helper_load(unsigned size,
	       struct abstract_interpret_value addr,
	       struct abstract_interpret_value rsp)
{
	struct expression_result res;
	unsigned char dummy_buf[16];

	interpreter_do_load(&res, size, addr.v);

	load_event((const void *)addr.v, size, dummy_buf, rsp.v);

	return res;
}

static void
do_helper_store(unsigned size,
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

#define strcmp(x, y) VG_(strcmp)((Char *)(x), (Char *)y)

/* XXX We don't track dependencies through dirty calls at all.  Oh
 * well. */
static void
do_dirty_call(struct interpret_state *is,
	      VexGuestArchState *state,
	      IRSB *irsb,
	      IRDirty *details)
{
	struct expression_result guard;
	struct expression_result args[6];
	unsigned x;
	unsigned long res;

	if (details->guard) {
		eval_expression(is, &guard, details->guard);
		send_expression(guard.lo.origin);
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
			do_helper_load(1, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		is->temporaries[details->tmp] =
			do_helper_load(2, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		is->temporaries[details->tmp] =
			do_helper_load(4, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		is->temporaries[details->tmp] =
			do_helper_load(8, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		is->temporaries[details->tmp] =
			do_helper_load(16, args[0].lo, args[1].lo);
	} else if (!strcmp(details->cee->name, "helper_store_8")) {
		do_helper_store(1, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_16")) {
		do_helper_store(2, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_32")) {
		do_helper_store(4, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_64")) {
		do_helper_store(8, args[0].lo, args[1], args[2].lo);
	} else if (!strcmp(details->cee->name, "helper_store_128")) {
		args[1].hi = args[2].lo;
		do_helper_store(16, args[0].lo, args[1], args[3].lo);
	} else {
		VG_(printf)("Unknown dirty call %s\n", details->cee->name);
		commit_interpreter_state();

		if (details->needsBBP) {
			res = ((unsigned long (*)(VexGuestArchState *,
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
				expr_imported();
			is->temporaries[details->tmp].hi.v = 0;
			is->temporaries[details->tmp].hi.origin = NULL;
		}
	}
}

static void initialise_is_for_vex_state(struct interpret_state *is,
					const VexGuestArchState *state);
static void syscall_event(VexGuestAMD64State *state);

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

	addr = istate->rip.v;
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

	if (record_nr > NOISY_AFTER_RECORD)
		ppIRSB(irsb);

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
		if (record_nr > NOISY_AFTER_RECORD) {
			VG_(printf)("Interpreting record %d ", record_nr);
			ppIRStmt(stmt);
			VG_(printf)("\n");
		}
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
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

			case Ity_I64:
				tl_assert(byte_offset == 0);
				*dest = data.lo;
				break;

			case Ity_I128:
			case Ity_V128:
				VG_(printf)("Put %lx:%lx to %x\n",
					    data.lo.v, data.hi.v, stmt->Ist.Put.offset);
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
			do_dirty_call(istate, state, irsb, stmt->Ist.Dirty.details);
			break;
		}

		case Ist_Exit: {
			struct expression_result guard;
			if (stmt->Ist.Exit.guard) {
				eval_expression(istate, &guard, stmt->Ist.Exit.guard);
				send_expression(guard.lo.origin);
				if (!guard.lo.v)
					break;
			}
			tl_assert(stmt->Ist.Exit.jk == Ijk_Boring);
			tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
			istate->rip.v = stmt->Ist.Exit.dst->Ico.U64;
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
		struct expression_result next_addr;
		eval_expression(istate, &next_addr, irsb->next);
		tl_assert(next_addr.hi.origin == NULL);
		send_expression(next_addr.lo.origin);
		istate->rip.v = next_addr.lo.v;
	}

	if (irsb->jumpkind == Ijk_Sys_syscall) {
		commit_interpreter_state();
		syscall_event(state);
		initialise_interpreter_state();
	}

finished_block:
	for (x = 0; x < irsb->tyenv->types_used; x++) {
		free_expression(istate->temporaries[x].lo.origin);
	}
	VG_(free)(istate->temporaries);
	istate->temporaries = NULL;

	gc_expressions();

	state->guest_RIP = istate->rip.v;

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
footstep_event(Addr rip, Word rdx, Word rcx, Word rax, unsigned long xmm3a,
	       unsigned long xmm0a)
{
	if (!current_thread->in_monitor) {
		TRACE(FOOTSTEP, rip, rdx, rcx, rax);
		if (use_footsteps)
			event(EVENT_footstep, rip, rdx, rcx, rax, xmm3a,
			      xmm0a);
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
reason_data(const struct expression *e1, const struct expression *e2)
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

	while (1) ;

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
#define CHECK_REG(i)							\
		replay_assert_eq(					\
			reason_data(expr_imported(),			\
				    expr_const(fr-> FOOTSTEP_REG_ ## i ## _NAME ) ), \
			fr-> FOOTSTEP_REG_ ## i ## _NAME,		\
			args[i+1])
		CHECK_REG(0);
		CHECK_REG(1);
		CHECK_REG(2);
		CHECK_REG(3);
		CHECK_REG(4);
#undef CHECK_REG
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
	aiv->v = value;
	aiv->origin = expr_imported();
}

static void
initialise_is_for_vex_state(struct interpret_state *is,
			    const VexGuestArchState *state)
{
	unsigned x;
	for (x = 0; x < 16; x++)
		init_register(&is->gregs[x], (&state->guest_RAX)[x]);
	init_register(&is->rip, state->guest_RIP);

	init_register(&is->cc_op, state->guest_CC_OP);
	init_register(&is->cc_dep1, state->guest_CC_DEP1);
	init_register(&is->cc_dep2, state->guest_CC_DEP2);
	init_register(&is->cc_ndep, state->guest_CC_NDEP);

	init_register(&is->d_flag, state->guest_DFLAG);
	init_register(&is->fs_zero, state->guest_FS_ZERO);

	for (x = 0; x < 32; x++)
		init_register(&is->xmm[x],
			      ((unsigned long *)&state->guest_XMM0)[x]);
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
	aiv->origin = NULL;
	return aiv->v;
}

static void
commit_is_to_vex_state(struct interpret_state *is,
		       VexGuestArchState *state)
{
	unsigned x;
	for (x = 0; x < 16; x++)
		(&state->guest_RAX)[x] = commit_register(&is->gregs[x]);
	state->guest_RIP = commit_register(&is->rip);

	state->guest_CC_OP = commit_register(&is->cc_op);
	state->guest_CC_DEP1 = commit_register(&is->cc_dep1);
	state->guest_CC_DEP2 = commit_register(&is->cc_dep2);
	state->guest_CC_NDEP = commit_register(&is->cc_ndep);

	state->guest_DFLAG = commit_register(&is->d_flag);
	state->guest_FS_ZERO = commit_register(&is->fs_zero);

	for (x = 0; x < 16; x++)
		((unsigned long *)&state->guest_XMM0)[x] =
			commit_register(&is->xmm[x]);
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
