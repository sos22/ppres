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
struct response_ancillary {
	unsigned code;
	unsigned nr_args;
};

struct response_string {
	unsigned len;
};
