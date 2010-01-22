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
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "libvex_trc_values.h"
#include "valgrind.h"

#include "ppres.h"
#include "coroutines.h"
#include "replay.h"
#include "replay2.h"

/* What kinds of records are we allowed to use? */
#define USE_FOOTSTEP_RECORDS 0

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
extern void VG_(client_syscall) ( ThreadId tid, UInt trc );
extern SysRes VG_(am_mmap_anon_fixed_client)( Addr start, SizeT length, UInt prot );

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

struct replay_thread {
	struct replay_thread *next;
	struct coroutine coroutine;
	ThreadId id;

	/* Hack: when we come back after satisfying a rdtsc, this is
	 * what we return. */
	ULong rdtsc_result;

	Bool failed;
	Bool dead;
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
			long thread;
			long nr;
		} runm;
	} u;
};

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

/* Bits for managing the transitions between client code and the
   replay monitor. */

/* Run the client thread until it generates an event, and figure out
   what that event was. */
static void
run_thread(struct replay_thread *rt, struct client_event_record *cer)
{
	tl_assert(!VG_(in_generated_code));
	tl_assert(client_event == NULL);
	tl_assert(current_thread == NULL);
	tl_assert(VG_(running_tid) == VG_INVALID_THREADID);
	tl_assert(!rt->dead);

	cer->type = EVENT_nothing;
	current_thread = rt;
	client_event = cer;
	VG_(running_tid) = rt->id;

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
#if USE_FOOTSTEP_RECORDS
	event(EVENT_footstep, rip, rdx, rcx, rax);
#endif
}

static void
syscall_event(VexGuestAMD64State *state)
{
	event(EVENT_syscall, state->guest_RAX, state->guest_RDI,
	      state->guest_RSI, state->guest_RDX, (unsigned long)state);
}

static ULong
rdtsc_event(void)
{
	event(EVENT_rdtsc);
	return current_thread->rdtsc_result;
}

static void
load_event(const void *ptr, unsigned size, void *read_bytes)
{
	if (trace_mode)
		VG_(printf)("%d: Load %d from %p\n", record_nr, size, ptr);
	VG_(memcpy)(read_bytes, ptr, size);
	access_nr++;
	event(EVENT_load, (unsigned long)ptr, size,
	      (unsigned long)read_bytes);
}

static void
store_event(void *ptr, unsigned size, const void *written_bytes)
{
	if (trace_mode)
		VG_(printf)("%d: Store %d to %p\n", record_nr, size, ptr);
	VG_(memcpy)(ptr, written_bytes, size);
	access_nr++;
	event(EVENT_store, (unsigned long)ptr, size,
	      (unsigned long)written_bytes);
}

static Bool
client_request_event(ThreadId tid, UWord *arg_block, UWord *ret)
{
	if (VG_IS_TOOL_USERREQ('P', 'P', arg_block[0])) {
		/* We are in generated code here, despite what
		   Valgrind might think about it. */
		VG_(in_generated_code) = True;
		event(EVENT_client_request, arg_block[0], arg_block[1]);
		VG_(in_generated_code) = False;
		*ret = 0;
		return True;
	} else if (VG_IS_TOOL_USERREQ('E', 'A', arg_block[0])) {
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
send_response(int res)
{
	safeish_write(control_process_socket, &res, sizeof(res));
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

static void
replay_failed(void)
{
	struct control_command cmd;

	send_response(1);
	while (1) {
		get_control_command(&cmd);
		if (cmd.cmd != WORKER_KILL) {
			VG_(printf)("Only the kill command is valid after replay fails\n");
			send_response(1);
			continue;
		}
		send_response(0);
		my__exit(0);
	}
}

#define replay_assert_eq(a, b)                                             \
do {                                                                       \
	if ((a) != (b)) {                                                  \
		VG_(printf)("%d: Replay failed at %d: %s(%lx) != %s(%lx)\n", \
	                    record_nr,                                     \
			    __LINE__,                                      \
                            #a,                                            \
			    (unsigned long)(a),				   \
			    #b,                                            \
			    (unsigned long)(b));			   \
		replay_failed();                                           \
	}                                                                  \
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
		replay_assert_eq(rec->cls, RECORD_footstep);
		replay_assert_eq(fr->rip, args[0]);
		replay_assert_eq(fr->rdx, args[1]);
		replay_assert_eq(fr->rcx, args[2]);
		replay_assert_eq(fr->rax, args[3]);
		return;
	}
	case EVENT_syscall: {
		const struct syscall_record *sr = payload;
		replay_assert_eq(rec->cls, RECORD_syscall);
		replay_assert_eq(sr->syscall_nr, args[0]);
		replay_assert_eq(sr->arg1, args[1]);
		replay_assert_eq(sr->arg2, args[2]);
		replay_assert_eq(sr->arg3, args[3]);
		return;
	}
	case EVENT_rdtsc: {
		replay_assert_eq(rec->cls, RECORD_rdtsc);
		return;
	}
	case EVENT_load: {
		const struct mem_read_record *mrr = payload;
		replay_assert_eq(rec->cls, RECORD_mem_read);
		replay_assert_eq(mrr->ptr, (void *)args[0]);
		replay_assert_eq(rec->size - sizeof(*rec) - sizeof(*mrr),
				 args[1]);
		switch (args[1]) {
		case 1:
			replay_assert_eq(*(unsigned char *)(mrr + 1),
					 *(unsigned char *)args[2]);
			break;
		case 2:
			replay_assert_eq(*(unsigned short *)(mrr + 1),
					 *(unsigned short *)args[2]);
			break;
		case 4:
			replay_assert_eq(*(unsigned *)(mrr + 1),
					 *(unsigned *)args[2]);
			break;
		case 8:
			replay_assert_eq(*(unsigned long *)(mrr + 1),
					 *(unsigned long *)args[2]);
			break;
		case 16:
			replay_assert_eq(((unsigned long *)(mrr + 1))[0],
					 ((unsigned long *)args[2])[0]);
			replay_assert_eq(((unsigned long *)(mrr + 1))[1],
					 ((unsigned long *)args[2])[1]);
			break;
		default:
			ASSUME(0);
		}
		return;
	}
	case EVENT_store: {
		const struct mem_read_record *mwr = payload;
		replay_assert_eq(rec->cls, RECORD_mem_write);
		replay_assert_eq(mwr->ptr, (void *)args[0]);
		replay_assert_eq(rec->size - sizeof(*rec) - sizeof(*mwr),
				 args[1]);
		switch (args[1]) {
		case 1:
			replay_assert_eq(*(unsigned char *)(mwr + 1),
					 *(unsigned char *)args[2]);
			break;
		case 2:
			replay_assert_eq(*(unsigned short *)(mwr + 1),
					 *(unsigned short *)args[2]);
			break;
		case 4:
			replay_assert_eq(*(unsigned *)(mwr + 1),
					 *(unsigned *)args[2]);
			break;
		case 8:
			replay_assert_eq(*(unsigned long *)(mwr + 1),
					 *(unsigned long *)args[2]);
			break;
		case 16:
			replay_assert_eq(((unsigned long *)(mwr + 1))[0],
					 ((unsigned long *)args[2])[0]);
			replay_assert_eq(((unsigned long *)(mwr + 1))[1],
					 ((unsigned long *)args[2])[1]);
			break;
		default:
			ASSUME(0);
		}
		return;
	}
	case EVENT_client_request: {
		const struct client_req_record *crr = payload;
		replay_assert_eq(rec->cls, RECORD_client);
		replay_assert_eq(args[0], crr->flavour);
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
		VG_(printf)("%d: Thread %d exits.\n", record_nr, rt->id);
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
		if (!sr_isError(sr->syscall_res)) {
			VG_(printf)("%d: Spawning a new thread.\n", record_nr);
			VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);
		}

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

	while (access_nr < nr_accesses) {
		run_thread(thr, &cer);
		if (cer.type == EVENT_footstep)
			continue;
		if (cer.type != EVENT_load &&
		    cer.type != EVENT_store) {
			VG_(printf)("%d: Client made unexpected event %x\n",
				    record_nr,
				    cer.type);
			replay_failed();
		}
	}
}

static void
run_for_n_records(struct record_consumer *logfile,
		  unsigned nr_records)
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
		    (!USE_FOOTSTEP_RECORDS &&
		     rec->cls == RECORD_footstep)) {
			finish_this_record(logfile);
			continue;
		}

		record_nr++;

		tl_assert(rec->cls != RECORD_memory);

		thr = get_thread_by_id(rec->tid);
		tl_assert(thr != NULL);

		ASSUME(!thr->failed);

		run_thread(thr, &thread_event);

		ASSUME(thread_event.type != EVENT_resched_candidate);

		validate_event(rec, &thread_event);

		replay_record(rec, thr, &thread_event, logfile); /* Finishes the record */
	}
}

static void
run_control_command(struct control_command *cmd, struct record_consumer *logfile)
{
	struct replay_thread *rt;

	switch (cmd->cmd) {
	case WORKER_KILL:
		send_response(0);
		my__exit(0);
	case WORKER_RUN:
		run_for_n_records(logfile, cmd->u.run.nr);
		send_response(0);
		break;
	case WORKER_TRACE:
		trace_mode = True;
		run_for_n_records(logfile, cmd->u.trace.nr);
		trace_mode = False;
		send_response(0);
		break;
	case WORKER_RUNM:
		rt = get_thread_by_id(cmd->u.runm.thread);
		if (!rt) {
			VG_(printf)("Cannot find thread %ld\n", cmd->u.runm.thread);
			send_response(-1);
		} else {
			run_for_n_mem_accesses(rt, cmd->u.runm.nr);
			send_response(0);
		}
		break;
	case WORKER_SNAPSHOT:
		control_process_socket = do_snapshot(control_process_socket);
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

	VG_(printf)("Replay machine starting.\n");

	open_logfile(&logfile, (Char *)"logfile1");

	while (1) {
		get_control_command(&cmd);
		run_control_command(&cmd, &logfile);
	}

	VG_(printf)("Hit end of log.\n");
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

	VG_(printf)("Running replay machine.\n");
	run_coroutine(&head_thread->coroutine, &replay_machine,
		      "start of day");
	VG_(printf)("Replay machine starts the world.\n");

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
	VG_(printf)("%d: In new thread\n", record_nr);
	if (!creating_new_thread) {
		VG_(printf)("Main thread\n");
		return;
	}

	newly_spawning_thread->id = VG_(running_tid);
	newly_spawning_thread->next = head_thread;
	head_thread = newly_spawning_thread;

	VG_(printf)("New thread is id %d, switching back to parent.\n",
		    VG_(running_tid));
	run_coroutine(&newly_spawning_thread->coroutine,
		      &creating_thread_coroutine,
		      "new_thread_starting");
	VG_(printf)("New thread starts for real in %d\n", VG_(running_tid));
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
	VG_(printf)("%d: Clone syscall\n", record_nr);

	tl_assert(VG_(running_tid) == VG_INVALID_THREADID);
	tl_assert(!creating_new_thread);
	creating_new_thread = True;

	initialise_coroutine(&creating_thread_coroutine, "creating thread coroutine");

	VG_(printf)("Current thread %p, id %d\n", current_thread,
		    VG_(running_tid));

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

	VG_(printf)("New thread spawned, my id now %d\n",
		    VG_(running_tid));
	tl_assert(creating_new_thread);
	creating_new_thread = False;

	return 0xaabbccdd;
}

static void
fini(Int ignore)
{
	VG_(printf)("Huh? Didn't expect fini() to get called.\n");
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
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
