#include "coroutines.h"

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

struct abstract_interpret_value {
	unsigned long v;
	const struct expression *origin;
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

struct interpret_mem_lookaside {
	struct interpret_mem_lookaside *next;
	Addr ptr;
	unsigned size;
	struct abstract_interpret_value aiv;
};

extern struct replay_thread *head_thread;
extern struct replay_thread *current_thread;
extern struct interpret_mem_lookaside *head_interpret_mem_lookaside;
extern unsigned record_nr;

int ui_loop(void);
int do_snapshot(int parent_fd);

long my__exit(int code);
long my_fork(void);
int socketpair(int domain, int type, int protocol, int *fds);
void safeish_write(int fd, const void *buffer, size_t buffer_size);
void safeish_read(int fd, void *buffer, size_t buffer_size);

struct msghdr;
size_t recvmsg(int sockfd, struct msghdr *msg, int flags);
size_t sendmsg(int sockfd, const struct msghdr *msg, int flags);


const struct expression *expr_reg(unsigned reg);
const struct expression *expr_const(unsigned long c);
const struct expression *expr_mem(void *ptr, unsigned size);
#define expr_mem1(p) expr_mem((p), 1)
#define expr_mem2(p) expr_mem((p), 2)
#define expr_mem4(p) expr_mem((p), 4)
#define expr_mem8(p) expr_mem((p), 8)
const struct expression *expr_not(const struct expression *e);
const struct expression *expr_imported(void);
#define BINOP_EXPR(n)							\
	const struct expression *expr_ ## n(const struct expression *,	\
					    const struct expression *)
BINOP_EXPR(sub);
BINOP_EXPR(add);
BINOP_EXPR(mul);
BINOP_EXPR(mul_hi);
BINOP_EXPR(muls);
BINOP_EXPR(and);
BINOP_EXPR(or);
BINOP_EXPR(xor);
BINOP_EXPR(shrl);
BINOP_EXPR(shra);
BINOP_EXPR(shl);
BINOP_EXPR(combine);
BINOP_EXPR(le);
BINOP_EXPR(be);
BINOP_EXPR(eq);
BINOP_EXPR(b);

void gc_expressions(void);

UInt interpret_log_control_flow(VexGuestAMD64State *state);
void initialise_interpreter_state(void);
void commit_interpreter_state(void);
IRSB *instrument_func(VgCallbackClosure *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

void load_event(const void *ptr, unsigned size, void *read_bytes,
		unsigned long rsp);
void store_event(void *ptr, unsigned size, const void *written_bytes,
		 unsigned long rsp);
void footstep_event(Addr rip, Word rdx, Word rcx, Word rax,
		    unsigned long xmm3a, unsigned long xmm0a);
void syscall_event(VexGuestAMD64State *state);
void send_expression(const struct expression *e);
void send_non_const_expression(const struct expression *e);

void _send_ancillary(unsigned code, unsigned nr_args, const unsigned long *args);
#define send_ancillary(_code, ...)                         \
do {						           \
	const unsigned long args[] = {__VA_ARGS__};	   \
	_send_ancillary((_code),			   \
			sizeof(args)/sizeof(args[0]),	   \
			args);				   \
} while (0)


/* ASSUME is like assert, in that it terminates if the argument is
   anything other than true, but it's supposed to be a hint that we're
   failing because something isn't implemented rather than because of
   a strict bug. */
#define ASSUME tl_assert




#define WORKER_SNAPSHOT 0x1234
#define WORKER_KILL 0x1235
#define WORKER_RUN 0x1236
#define WORKER_TRACE 0x1237
#define WORKER_RUNM 0x1238
#define WORKER_TRACE_THREAD 0x1239
#define WORKER_TRACE_ADDRESS 0x123a
#define WORKER_THREAD_STATE 0x123b
#define WORKER_REPLAY_STATE 0x123c
#define WORKER_CONTROL_TRACE 0x123d

struct command_header {
	unsigned command;
	unsigned nr_args;
};

#define RESPONSE_OKAY 0
#define RESPONSE_ERR 1
#define RESPONSE_ANCILLARY 2
#define RESPONSE_STRING 3
struct response_message {
	unsigned response;
};

#define ANCILLARY_TRACE_FOOTSTEP 1
#define ANCILLARY_TRACE_SYSCALL 2
#define ANCILLARY_TRACE_RDTSC 3
#define ANCILLARY_TRACE_LOAD 4
#define ANCILLARY_TRACE_STORE 5
#define ANCILLARY_TRACE_CALLING 6
#define ANCILLARY_TRACE_CALLED 7
#define ANCILLARY_TRACE_ENTER_MONITOR 8
#define ANCILLARY_TRACE_EXIT_MONITOR 9
#define ANCILLARY_REPLAY_SUCCESS 10
#define ANCILLARY_REPLAY_FAILED 11
#define ANCILLARY_EXPRESSION 12
struct response_ancillary {
	unsigned code;
	unsigned nr_args;
};

struct response_string {
	unsigned len;
};

#define REASON_CONTROL 0
#define REASON_DATA 1
#define REASON_OTHER 2

/* These must be in the same order as the fields in VEX's guest state
   structure. */
#define REG_RAX 0
#define REG_RCX 1
#define REG_RDX 2
#define REG_RBX 3
#define REG_RSP 4
#define REG_RBP 5
#define REG_RSI 6
#define REG_RDI 7

#define EXPR_CONST 0
#define EXPR_REG 1
#define EXPR_MEM 2
#define EXPR_IMPORTED 3

#define EXPR_COMBINE 4

#define EXPR_SUB 5
#define EXPR_ADD 6
#define EXPR_MUL 7
#define EXPR_MUL_HI 8
#define EXPR_MULS 9

#define EXPR_SHRL 10
#define EXPR_SHL 11
#define EXPR_SHRA 12

#define EXPR_AND 13
#define EXPR_OR 14
#define EXPR_XOR 15

#define EXPR_LE 16
#define EXPR_BE 17
#define EXPR_EQ 18
#define EXPR_B 19

#define EXPR_BINOP_FIRST EXPR_COMBINE
#define EXPR_BINOP_LAST EXPR_B

#define EXPR_NOT 20

