#include "coroutines.h"


#define WORKER_SNAPSHOT 0x1234
#define WORKER_KILL 0x1235
#define WORKER_RUN 0x1236
#define WORKER_TRACE 0x1237


#define WORKER_TRACE_ADDRESS 0x123a
#define WORKER_THREAD_STATE 0x123b
#define WORKER_REPLAY_STATE 0x123c
#define WORKER_CONTROL_TRACE 0x123d
#define WORKER_GET_MEMORY 0x123e
#define WORKER_VG_INTERMEDIATE 0x123f
#define WORKER_GET_THREAD 0x1240
#define WORKER_SET_THREAD 0x1241
#define WORKER_GET_REGISTERS 0x1242

struct command_header {
	unsigned command;
	unsigned nr_args;
};

#define RESPONSE_OKAY 0
#define RESPONSE_ERR 1
#define RESPONSE_ANCILLARY 2
#define RESPONSE_STRING 3
#define RESPONSE_BYTES 4
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
#define ANCILLARY_THREAD_STATE 13
#define ANCILLARY_REPLAY_FINISHED 14
#define ANCILLARY_NEXT_THREAD 15
#define ANCILLARY_REG_BINDING 16
#define ANCILLARY_TRACE_SIGNAL 17
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
#define REG_R8 8
#define REG_R9 9
#define REG_R10 10
#define REG_R11 11
#define REG_R12 12
#define REG_R13 13
#define REG_R14 14
#define REG_R15 15
#define REG_CC_OP 16
#define REG_CC_DEP1 17
#define REG_CC_DEP2 18
#define REG_CC_NDEP 19
#define REG_DFLAG 20
#define REG_RIP 21
#define REG_IDFLAG 22
#define REG_FS_ZERO 23
#define REG_SSE_ROUND 24

/* Rather than 16 128 bit registers, we pretend there are 32 64 bit
 * ones. */
#define REG_XMM0 25
#define REG_XMM_LAST (REG_XMM0 + 32)

#define REG_LAST REG_XMM_LAST


#define EXPR_CONST 0
#define EXPR_REG 1
#define EXPR_LOAD 2
#define EXPR_STORE 3
#define EXPR_IMPORTED 4

#define EXPR_COMBINE 5

#define EXPR_SUB 6
#define EXPR_ADD 7
#define EXPR_MUL 8
#define EXPR_MUL_HI 9
#define EXPR_MULS 10

#define EXPR_SHRL 11
#define EXPR_SHL 12
#define EXPR_SHRA 13

#define EXPR_AND 14
#define EXPR_OR 15
#define EXPR_XOR 16

#define EXPR_LE 17
#define EXPR_BE 18
#define EXPR_EQ 19
#define EXPR_B 20

#define EXPR_LOGICAL_FIRST EXPR_LE
#define EXPR_LOGICAL_LAST EXPR_B

#define EXPR_BINOP_FIRST EXPR_COMBINE
#define EXPR_BINOP_LAST EXPR_B

#define EXPR_NOT 21


typedef struct {
	unsigned long access_nr;
} replay_coord_t;


extern Bool VG_(in_generated_code);



struct expression {
	unsigned type;
	union {
		struct {
			unsigned name;
			unsigned long val;
		} reg;
		struct {
			unsigned long val;
			struct expression *next, *prev;
		} cnst;
		struct {
			unsigned long val;
		} imported;
		struct {
			replay_coord_t when;
			unsigned size;
			ThreadId tid; /* This is, strictly speaking,
					 redundant, because it's
					 implied by @when, but it's a
					 pain to derive it later and
					 very easy to record when we
					 make the expression, so stash
					 it here. */

			const struct expression *ptr_e;
			const struct expression *val;
		} load;
		struct {
			replay_coord_t when;
			ThreadId tid; /* Redundant, but see comments
					 for load. */
			const struct expression *val;
		} store;
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

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
};

struct interpret_state {
	Bool live;
	unsigned nr_temporaries;
	struct expression_result *temporaries;
	struct abstract_interpret_value registers[REG_LAST+1];
	const struct expression *hazard[2];
};

struct replay_thread {
	struct replay_thread *next;
	struct coroutine coroutine;
	ThreadId id;

	/* Hack: when we come back after satisfying a rdtsc, this is
	 * what we return. */
	ULong rdtsc_result;

	replay_coord_t last_run;
	Bool dead;
	Bool in_monitor;
	Bool blocked;

	/* The RIP last time we ran an instruction in this thread.
	   Collected from the footstep events.  Ignores monitor
	   events. */
	Word last_rip;

	struct interpret_state interpret_state;
};

struct interpret_mem_lookaside {
	struct interpret_mem_lookaside *next;
	Addr ptr;
	unsigned size;
	struct abstract_interpret_value aiv;
};

struct control_command {
	unsigned cmd;
	union {
		struct {
			replay_coord_t when;
		} run;
		struct {
			replay_coord_t when;
		} trace;
		struct {
			replay_coord_t when;
		} control_trace;
		struct {
			long address;
			replay_coord_t when;
		} trace_mem;
		struct {
			unsigned long addr;
			unsigned long size;
		} get_memory;
		struct {
			unsigned long addr;
		} vg_intermediate;
		struct {
			long tid;
		} set_thread;
	} u;
};

enum event_type { EVENT_nothing = 0xf001,
		  EVENT_footstep,
		  EVENT_syscall,
		  EVENT_rdtsc,
		  EVENT_load,
		  EVENT_store,
		  EVENT_client_request,
		  EVENT_signal };

struct client_event_record {
	enum event_type type;
	unsigned nr_args;

	/* Careful: this is on the stack of the thread which generated
	   the event, so it becomes invalid as soon as that thread
	   gets scheduled. */
	const unsigned long *args;
};

extern struct replay_thread *head_thread;
extern struct replay_thread *current_thread;
extern struct interpret_mem_lookaside *head_interpret_mem_lookaside;
extern struct client_event_record *client_event;
extern struct record_consumer logfile;
extern replay_coord_t now;
extern Bool want_to_interpret;

int ui_loop(void);
int do_snapshot(int parent_fd);

long my__exit(int code);
long my_fork(void);
void my_sleep(unsigned x);
int socketpair(int domain, int type, int protocol, int *fds);
void safeish_write(int fd, const void *buffer, size_t buffer_size);
void safeish_read(int fd, void *buffer, size_t buffer_size);
Bool safe_memcpy(void *dest, const void *src, unsigned size);

struct msghdr;
size_t recvmsg(int sockfd, struct msghdr *msg, int flags);
size_t sendmsg(int sockfd, const struct msghdr *msg, int flags);


const struct expression *expr_reg(unsigned reg, unsigned long val);
const struct expression *expr_const(unsigned long c);
const struct expression *expr_load(unsigned size, const struct expression *ptr,
				   const struct expression *val);
const struct expression *expr_store(const struct expression *val);
const struct expression *expr_not(const struct expression *e);
const struct expression *expr_imported(unsigned long value);
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
void disassemble_addr(unsigned long addr);
IRSB *instrument_func(VgCallbackClosure *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

void load_event(const void *ptr, unsigned size, void *read_bytes,
		unsigned long rsp, unsigned long rip);
void store_event(void *ptr, unsigned size, const void *written_bytes,
		 unsigned long rsp, unsigned long rip);
void footstep_event(Addr rip, Word rdx, Word rcx, Word rax,
		    unsigned long xmm3a, unsigned long xmm0a);
void syscall_event(VexGuestAMD64State *state);
Bool client_request_event(ThreadId tid, UWord *arg_block, UWord *ret);

void send_expression(const struct expression *e);
void send_non_const_expression(const struct expression *e);
void ref_expression_result(struct interpret_state *is,
			   const struct expression_result *er);
void deref_expression_result(struct interpret_state *is,
			     const struct expression_result *er);

void _send_ancillary(unsigned code, unsigned nr_args, const unsigned long *args);
#define send_ancillary(_code, ...)                         \
do {						           \
	const unsigned long args[] = {__VA_ARGS__};	   \
	_send_ancillary((_code),			   \
			sizeof(args)/sizeof(args[0]),	   \
			args);				   \
} while (0)


void _client_event(void);
#define event(_code, ...)					  \
do {                                                              \
	unsigned long args[] = {__VA_ARGS__};			  \
	client_event->type = (_code);                             \
	client_event->nr_args = sizeof(args) / sizeof(args[0]);   \
	client_event->args = args;                                \
	_client_event();                                          \
} while (0)


void debug_control_command(const struct control_command *cc);
void _debug_trace_data(unsigned code, unsigned thread, unsigned nr_args, const unsigned long *args);
#define debug_trace_data(_code, ...)					\
	do {								\
		const unsigned long _args[] = {__VA_ARGS__};		\
		_debug_trace_data((_code),				\
				  current_thread->id,			\
				  sizeof(_args)/sizeof(_args[0]),	\
				  _args);				\
	} while (0)
void debugger_attach(void);
void check_fpu_control(void);
void load_fpu_control(void);

/* ASSUME is like assert, in that it terminates if the argument is
   anything other than true, but it's supposed to be a hint that we're
   failing because something isn't implemented rather than because of
   a strict bug. */
#define ASSUME tl_assert



