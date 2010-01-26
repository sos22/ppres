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

#define REG_RAX 0
#define REG_RDX 1
#define REG_RCX 2
#define REG_RBX 3
#define REG_RSP 4
#define REG_RBP 5
#define REG_RSI 6
#define REG_RDI 7

#define EXPR_CONST 0
#define EXPR_REG 1
#define EXPR_MEM 2
#define EXPR_IMPORTED 3
#define EXPR_SUB 4
#define EXPR_SHRL 5
#define EXPR_AND 6
#define EXPR_SHL 7
#define EXPR_COMBINE 8
#define EXPR_OR 9
#define EXPR_ADD 10
#define EXPR_LE 11
#define EXPR_BE 12
#define EXPR_SHRA 13
#define EXPR_EQ 14
#define EXPR_XOR 15

#define EXPR_MUL 16
#define EXPR_MUL_HI 17

#define EXPR_NOT 18

#define EXPR_B 19
