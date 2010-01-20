/* The replay engine itself.  We structure this as, effectively, a
   pair of co-routines.  One of the co-routines runs the client code
   and the other one runs the replay engine state machine.  For
   multithreaded clients, there's one coroutine per client thread.

   We don't bother creating OS threads for client threads.  That means
   making some moderately invasive changes to the Valgrind core, but
   makes it much easier for us to control the scheduling with the
   required precision.
*/
#include <asm/unistd.h>
#include <sys/mman.h>
#include <sys/fcntl.h>
#include <sys/wait.h>
#include <linux/utsname.h>
#include <linux/sched.h>
#include <linux/futex.h>
#include <setjmp.h>
#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_vki.h"
#include "pub_tool_signals.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_libcsignal.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "libvex_trc_values.h"

#include "valgrind.h"

#include "ppres.h"
#include "replay.h"
#include "coroutines.h"
#include "schedule.h"
#include "races.h"
#include "list.h"

#define DBG_SCHEDULE 0x1
#define DBG_EVENTS 0x2

#define debug_level (DBG_SCHEDULE|DBG_EVENTS)

#define DEBUG(lvl, fmt, args...)                               \
do {                                                           \
	if (debug_level & (lvl))                               \
		VG_(printf)("%d:%lx " fmt,                     \
			    current_thread->id,                \
			    logfile.offset_in_file +           \
                                 logfile.offset_in_current_chunk\
			    , ## args);                        \
} while (0)

/* Can the replay system see footstep records at all? */
#define SEARCH_USES_FOOTSTEPS 0

/* Can the replay system see memory records at all? */
#define SEARCH_USES_MEMORY 0

/* Setting this makes us reschedule on every memory access, rather
   than just the ones which might be racy. */
#define RESCHEDULE_ON_EVERY_MEMORY_ACCESS 0


/* Debug aid: we log every access to ``magic'' memory. */
static inline Bool
access_is_magic(const void *base, unsigned size)
{
#define MAGIC_ADDRESS ((void *)0)
	return base + size >= MAGIC_ADDRESS &&
		base < MAGIC_ADDRESS + 16;
#undef MAGIC_ADDRESS
}

#define NONDETERMINISM_POISON 0xf001dead
extern ThreadId VG_(running_tid);
extern Bool VG_(in_generated_code);
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

/* Shouldn't really be calling these from here.  Oh well. */
extern void VG_(client_syscall) ( ThreadId tid, UInt trc );
extern SysRes VG_(am_mmap_anon_fixed_client)( Addr start, SizeT length, UInt prot );

#define CSR_BUFFER 16

struct mem_access_event {
	Bool is_read; /* or write */
	void *ptr;
	unsigned size;
	unsigned char buffer[CSR_BUFFER];
};

enum thread_run_state {
	/* Thread is currently running */
	trs_running = 5678,

	/* Thread could run */
	trs_runnable,

	/* Thread is blocked waiting for an unblock record in the
	 * log */
	trs_blocked,

	/* Thread has failed. */
	trs_failed,

	/* Thread has exited */
	trs_dead,

	/* Thread is blocked awaiting a replay record. */
	trs_replay_blocked
};

struct replay_thread {
	struct replay_thread *next_thread;
	struct coroutine coroutine;
	ThreadId id;
	ThreadId parent_id;
	Bool in_generated;
	Bool blocked_by_log;
	enum thread_run_state run_state;
};

static struct replay_thread *
head_thread, *
current_thread;
static struct execution_schedule
execution_schedule;
static int
worker_process_output_fd;

#define SEARCH_CODE_REPLAY_SUCCESS 0xa2b3c4d5
#define SEARCH_CODE_REPLAY_FAILURE 0xa2b3c4d6
#define SEARCH_CODE_NEW_RACE_ADDR 0xa2b3c4d7

static inline Word
syscall_sysnr(VexGuestAMD64State *state)
{
	return state->guest_RAX;
}

static inline Word
syscall_arg_1(VexGuestAMD64State *state)
{
	return state->guest_RDI;
}

static inline Word
syscall_arg_2(VexGuestAMD64State *state)
{
	return state->guest_RSI;
}

static inline Word
syscall_arg_3(VexGuestAMD64State *state)
{
	return state->guest_RDX;
}

static inline Word
syscall_arg_4(VexGuestAMD64State *state)
{
	return state->guest_RCX;
}


static struct record_consumer
logfile;

static void
my_mprotect(void *base, size_t len, int prot)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_mprotect), "rdi" (base),
	     "rsi" (len), "rdx" (prot));
}

static long
my__exit(int code)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_exit), "rdi" (code));
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


/* Switch to a different thread when we're in client code.  This is
   more tricky, because we need to get the monitor to do the switch
   for us.  When the function returns, we're in the same thread as we
   started in, but the target will have run for a bit. */
static void
_switch_thread_client(struct replay_thread *target, const char *msg,
		      va_list args)
{
	struct replay_thread *me = current_thread;

	tl_assert(target != current_thread);

	VG_(printf)("Client ctxt switch %d -> %d for ",
		    current_thread->id, target->id);
	VG_(vprintf)(msg, args);
	VG_(printf)("\n");

	current_thread->in_generated = VG_(in_generated_code);
	if (current_thread->run_state == trs_running)
		current_thread->run_state = trs_runnable;
	current_thread = target;
	current_thread->run_state = trs_running;

	tl_assert(current_thread == target);
	run_coroutine(&me->coroutine,
		      &current_thread->coroutine,
		      "_switch_thread_client");
	tl_assert(current_thread == me);

	VG_(in_generated_code) = current_thread->in_generated;
	VG_(running_tid) = current_thread->id;
}

static void
switch_thread_client(struct replay_thread *target, const char *msg,
		      ...)
{
	va_list args;
	va_start(args, msg);
	_switch_thread_client(target, msg, args);
	va_end(args);
}

static Bool
thread_runnable(const struct replay_thread *tr)
{
	switch (tr->run_state) {
	case trs_running:
	case trs_runnable:
		return True;
	case trs_blocked:
	case trs_failed:
	case trs_dead:
		return False;
	case trs_replay_blocked:
		return get_current_record(&logfile)->tid == tr->id;
	}

	VG_(tool_panic)((Char *)"Bad scheduling state");
}

static void
replay_run_finished(unsigned code)
{
	VG_(write)(worker_process_output_fd, &code, sizeof(code));
	my__exit(1);
}

static struct replay_thread *
select_new_thread(void)
{
	struct replay_thread *rt;
	unsigned other_threads;
	unsigned thread_to_run;
	unsigned x;

	other_threads = 0;
	rt = head_thread;
	while (rt != NULL) {
		if (rt != current_thread && thread_runnable(rt))
			other_threads++;
		rt = rt->next_thread;
	}

	if (other_threads == 0) {
		if (!thread_runnable(current_thread)) {
			/* Every thread is either failed or blocked,
			   so we can't continue.  Tell the driver that
			   we're dead. */
			VG_(printf)("Ran out of threads to run.\n");
			replay_run_finished(SEARCH_CODE_REPLAY_FAILURE);
		}
	}
	thread_to_run = make_nd_choice(&execution_schedule,
				       other_threads);
	tl_assert(thread_to_run <= other_threads);
	if (thread_to_run == 0 && thread_runnable(current_thread))
		return current_thread;

	rt = head_thread;
	if (rt == current_thread)
		rt = rt->next_thread;
	x = 1;
	while (x < thread_to_run) {
		rt = rt->next_thread;
		tl_assert(rt != NULL);
		while (rt == current_thread || !thread_runnable(rt))
			rt = rt->next_thread;
		x++;
	}

	tl_assert(rt != NULL);
	tl_assert(rt != current_thread);
	tl_assert(thread_runnable(rt));

	return rt;
}

/* Run another thread for a bit.  This doesn't return until we switch
   back to the original thread. */
static void
reschedule_client(Bool loud, const char *msg, ...)
{
	struct replay_thread *rt;
	va_list args;

	rt = select_new_thread();
	va_start(args, msg);
	if (rt == current_thread) {
		if (loud) {
			VG_(printf)("Keep in thread %d for ",
				    current_thread->id);
			VG_(vprintf)(msg, args);
			VG_(printf)("\n");
		}
	} else {
		_switch_thread_client(rt, msg, args);
	}
	va_end(args);
}

/* This thread has failed a validation, and so shouldn't be run any
   further. */
/* The semantics depend on whether you're in the monitor.  In the
   monitor, we pick another thread and return.  In client code, this
   function immediately schedules out and never returns. */
static void
failure(Bool finish, const char *fmt, ...)
{
	va_list args;

	if (!execution_schedule.failed)
		VG_(printf)("Replay failed after %ld bytes\n",
			    logfile.offset_in_file);
	va_start(args, fmt);
	VG_(vprintf)(fmt, args);
	va_end(args);
	VG_(printf)("In thread %d\n", current_thread->id);

	execution_schedule.failed = True;

	if (finish)
		finish_this_record(&logfile);

	/* Mark this thread as failed, but let every other thread
	   carry on, so that we have a better chance of finding
	   interesting races. */
	current_thread->run_state = trs_failed;
	reschedule_client(True, "thread failed");
	VG_(tool_panic)((Char *)"Running a failed thread!");
}

#define replay_assert(cond, msg, ...)                     \
do {                                                      \
	if (!(cond)) {                                    \
		failure(True, "Assertion %s failed at %d: " msg "\n",	\
                        #cond , __LINE__, ## __VA_ARGS__ );		\
                VG_(tool_panic)((Char *)"Failed thread rescheduled!"); \
	}                                                 \
} while (0)

static void *
_get_record_this_thread(struct record_header **out_rh)
{
	struct record_header *rh;

	rh = get_current_record(&logfile);
	if (rh->tid == current_thread->id) {
		*out_rh = rh;
		return rh + 1;
	}

	current_thread->run_state = trs_replay_blocked;
	reschedule_client(True, "waiting for log to catch up");
	rh = get_current_record(&logfile);
	tl_assert(rh->tid == current_thread->id);
	*out_rh = rh;
	return rh + 1;
}

static void *
get_record_this_thread(struct record_header **out_rh)
{
	void *res;

	while (1) {
		/* A block record is always followed by a syscall
		   record, for the syscall which caused us to block,
		   and then an unblock record.  Enforce that here, and
		   also filter out the block/unblock records. */
		res = _get_record_this_thread(out_rh);
		switch ((*out_rh)->cls) {
		case RECORD_thread_blocking:
			tl_assert(!current_thread->blocked_by_log);
			current_thread->blocked_by_log = True;
			DEBUG(DBG_SCHEDULE, "Thread %d blocked by log\n", current_thread->id);
			finish_this_record(&logfile);
			break;
		case RECORD_thread_unblocked:
			tl_assert(current_thread->blocked_by_log);
			current_thread->blocked_by_log = False;
			DEBUG(DBG_SCHEDULE, "Thread %d unblocked by log\n", current_thread->id);
			finish_this_record(&logfile);
			break;
#if !SEARCH_USES_FOOTSTEPS
		case RECORD_footstep:
			finish_this_record(&logfile);
			break;
#endif
#if !SEARCH_USES_MEMORY
		case RECORD_mem_read:
		case RECORD_mem_write:
			finish_this_record(&logfile);
			break;
#endif
		default:
			if (current_thread->blocked_by_log)
				tl_assert((*out_rh)->cls == RECORD_syscall);
			return res;
		}
	}
}

#if SEARCH_USES_FOOTSTEPS
static void
footstep_event(Addr rip, Word rdx, Word rcx, Word rax)
{
	struct footstep_record *fr;
	struct record_header *rh;

	DEBUG(DBG_EVENTS, "footstep_event(%lx, %lx, %lx, %lx)\n", rip, rdx, rcx, rax);

	reschedule_client(False, "footstep at %lx\n", rip);

	fr = get_record_this_thread(&rh);
	replay_assert(rh->cls == RECORD_footstep,
		      "wanted a footstep record in thread %d, got class %d (rip %lx)",
		      current_thread->id,
		      rh->cls,
		      rip);
	replay_assert(rip == fr->rip,
		      "wanted a footstep at %lx, got one at %lx, thread %d",
		      fr->rip, rip, current_thread->id);
	replay_assert(rax == fr->rax,
		      "RAX mismatch: %lx != %lx at %lx",
		      rax, fr->rax, rip);
	replay_assert(rdx == fr->rdx,
		      "RDX mismatch: %lx != %lx at %lx",
		      rdx, fr->rdx, rip);
	replay_assert(rcx == fr->rcx ||
		      rcx == NONDETERMINISM_POISON,
		      "RCX mismatch: %lx != %lx at %lx",
		      rcx, fr->rcx, rip);
	finish_this_record(&logfile);
}
#endif

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
		failure(False,
			"Signal trying to replay memory at %p -> thread failed\n",
			mr->ptr);
		return;
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
process_memory_records(void)
{
	struct record_header *rh;

	rh = get_current_record(&logfile);
	while (rh->cls == RECORD_memory) {
		replay_memory_record(rh, (struct memory_record *)(rh + 1));
		finish_this_record(&logfile);
		rh = get_current_record(&logfile);
	}
}

static void
syscall_event(VexGuestAMD64State *state)
{
	struct syscall_record *sr;
	struct record_header *rh;

	DEBUG(DBG_EVENTS, "syscall_event()\n");

	reschedule_client(False, "syscall %d", syscall_sysnr(state));

	sr = get_record_this_thread(&rh);
	tl_assert(rh->tid == current_thread->id);
	if (rh->cls == RECORD_new_thread) {
		/* We don't actually do anything in response to these.
		 * Ignore it. */
		finish_this_record(&logfile);
		sr = get_record_this_thread(&rh);
	}
	replay_assert(rh->cls == RECORD_syscall &&
		      rh->tid == current_thread->id,
		      "wanted a syscall record in thread %d, got class %d",
		      current_thread->id,
		      rh->cls);

	replay_assert(syscall_sysnr(state) == sr->syscall_nr,
		      "wanted syscall %d, got syscall %ld",
		      sr->syscall_nr,
		      syscall_sysnr(state));
	replay_assert(syscall_arg_1(state) == sr->arg1,
		      "wanted arg1 to be %lx, was %lx for syscall %d",
		      sr->arg1,
		      syscall_arg_1(state),
		      sr->syscall_nr);
	replay_assert(syscall_arg_2(state) == sr->arg2,
		      "wanted arg2 to be %lx, was %lx for syscall %d",
		      sr->arg2,
		      syscall_arg_2(state),
		      sr->syscall_nr);
	replay_assert(syscall_arg_3(state) == sr->arg3,
		      "wanted arg3 to be %lx, was %lx for syscall %d",
		      sr->arg3,
		      syscall_arg_3(state),
		      sr->syscall_nr);

	switch (sr->syscall_nr) {
		/* Very easy syscalls: don't bother running them, and
		   just drop in the recorded return value. */
	case __NR_access:
	case __NR_open:
	case __NR_read:
	case __NR_fstat:
	case __NR_uname:
	case __NR_getcwd:
	case __NR_close:
	case __NR_stat:
	case __NR_getrlimit:
	case __NR_clock_gettime:
	case __NR_lseek:

	case __NR_write: /* Should maybe do something special with
			    these so that we see stuff on stdout? */

	case __NR_nanosleep: /* XXX: We should arguably tweak the
				scheduler to prefer not to select this
				thread when we see one of these.
				Maybe later. */

		if (sr_isError(sr->syscall_res))
			state->guest_RAX = -sr_Err(sr->syscall_res);
		else
			state->guest_RAX = sr_Res(sr->syscall_res);
		finish_this_record(&logfile);
		break;

	case __NR_exit_group:
		VG_(printf)("exit_group syscall came up in log, arg1 %lx.\n",
			    syscall_arg_1(state));
		finish_this_record(&logfile);
		break;

	case __NR_exit:
		current_thread->run_state = trs_dead;
		finish_this_record(&logfile);
		reschedule_client(True, "thread exiting");
		VG_(tool_panic)((Char *)"Running a thread after it exitted!\n");
		break;

		/* Moderately easy syscalls: run them and assert that
		   the result is the same. */
	case __NR_brk:
	case __NR_mprotect:
	case __NR_arch_prctl:
	case __NR_munmap:
	case __NR_set_robust_list:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:
		VG_(client_syscall)(VG_(get_running_tid)(),
				    VEX_TRC_JMP_SYS_SYSCALL);
		if (sr_isError(sr->syscall_res))
			replay_assert(-state->guest_RAX == sr_Err(sr->syscall_res),
				      "Expected syscall to fail %d, actually got %d",
				      sr_Err(sr->syscall_res),
				      -state->guest_RAX);
		else
			replay_assert(state->guest_RAX == sr_Res(sr->syscall_res),
				      "expected syscall to succeed %d, actually got %d",
				      sr_Res(sr->syscall_res),
				      state->guest_RAX);
		finish_this_record(&logfile);
		break;

		/* Bizarre calling convention: returns the PID, so we need
		   to run the call and then shove the results in. */
	case __NR_set_tid_address:
		if (sr_isError(sr->syscall_res)) {
			state->guest_RAX = -sr_Err(sr->syscall_res);
		} else {
			VG_(client_syscall)(VG_(get_running_tid)(),
					    VEX_TRC_JMP_SYS_SYSCALL);
			state->guest_RAX = sr_Res(sr->syscall_res);
		}
		finish_this_record(&logfile);
		break;

	case __NR_clone:
		/* This is a bit awkward.  First, we need to manually
		   advance RIP over the syscall instruction, for
		   reasons which aren't particularly clear. */
		state->guest_RIP += 2;
		if (sr_isError(sr->syscall_res)) {
			state->guest_RAX = -sr_Err(sr->syscall_res);
		} else {
			/* Now we need to issue the clone syscall
			   itself.  This won't actually do a syscall
			   at the kernel level, because it'll get
			   trapped in replay_clone_syscall() and
			   turned into the creation of a
			   replay_thread. */
			DEBUG(DBG_SCHEDULE, "Spawning a new thread\n");
			VG_(client_syscall)(VG_(get_running_tid)(),
					    VEX_TRC_JMP_SYS_SYSCALL);
			DEBUG(DBG_SCHEDULE, "Done spawn, in parent\n");
			state->guest_RAX = sr_Res(sr->syscall_res);
		}
		finish_this_record(&logfile);
		break;

	case __NR_mmap: {
		Addr addr;
		ULong length;
		SysRes map_res;
		Word prot;

		if (sr_isError(sr->syscall_res)) {
			state->guest_RAX = -sr_Err(sr->syscall_res);
			finish_this_record(&logfile);
			break;
		}
		addr = sr_Res(sr->syscall_res);
		length = syscall_arg_2(state);
		prot = syscall_arg_3(state);
		/* Turn the mmap() into a fixed anonymous one. */
		/* The syscall record will be followed by a bunch of
		   memory write ones which will actually populate it
		   for us, but we need to fiddle with the page
		   protections to make sure that they can. */
		map_res = VG_(am_mmap_anon_fixed_client)(addr,
							 length,
							 prot | PROT_WRITE);
		tl_assert(!sr_isError(map_res));
		finish_this_record(&logfile);
		process_memory_records();
		if (!(prot & PROT_WRITE))
			my_mprotect((void *)addr, length, prot);
		state->guest_RAX = addr;
		break;
	}

	case __NR_futex:
		/* Don't need to do anything here: we have explicit
		   block/unblock records which tell us exactly what to
		   do. */
		if (sr_isError(sr->syscall_res))
			state->guest_RAX = -sr_Err(sr->syscall_res);
		else
			state->guest_RAX = sr_Res(sr->syscall_res);
		finish_this_record(&logfile);
		break;

	default:
		VG_(printf)("don't know how to replay syscall %lld yet\n",
			    state->guest_RAX);
		VG_(exit)(1);
	}


	process_memory_records();
}

static void
load_event(const void *ptr, unsigned size, void *read_contents)
{
#if SEARCH_USES_MEMORY
	struct mem_read_record *mrr;
	struct record_header *rh;
	int safe;
#endif

	DEBUG(DBG_EVENTS, "load_event(%p, %x)\n", ptr, size);
	if (access_is_magic(ptr, size))
		VG_(printf)("Thread %d load %d from %p\n",
			    current_thread->id,
			    size,
			    ptr);

	if (RESCHEDULE_ON_EVERY_MEMORY_ACCESS ||
	    racetrack_address_races((Addr)ptr, size))
		reschedule_client(False, "load %d from %p", size, ptr);

	racetrack_read_region((Addr)ptr, size, current_thread->id);

#if SEARCH_USES_MEMORY
	/* Need to grab the record before capturing memory, because
	   getting the record can force a reschedule, and we want to
	   pick up anything which gets written while we're away. */
	mrr = get_record_this_thread(&rh);
	replay_assert(rh->cls == RECORD_mem_read,
		      "wanted a memory read record in thread %d, got class %d",
		      current_thread->id,
		      rh->cls);
	replay_assert(ptr == mrr->ptr,
		      "wanted a read from %p, got one from %p",
		      mrr->ptr,
		      ptr);
	replay_assert(size == rh->size - sizeof(*rh) - sizeof(*mrr),
		      "wanted a read size %d, got one size %d",
		      rh->size - sizeof(*rh) - sizeof(*mrr),
		      size);

	VG_(memcpy)(read_contents, ptr, size);

	if (access_is_magic(ptr, size))
		VG_(printf)("Thread %d did load %d from %p -> %lx\n",
			    current_thread->id,
			    size,
			    ptr,
			    *(unsigned long *)ptr);

	safe = 1;
	if (VG_(memcmp)(read_contents, mrr + 1, size)) {
		safe = 0;
		if ((size == 4 && *(unsigned *)read_contents == NONDETERMINISM_POISON) ||
		    (size == 8 && *(unsigned long *)read_contents == NONDETERMINISM_POISON))
			safe = 1;
	}
	replay_assert(safe,
		      "memory read divergence at address %p: wanted %lx but got %lx (size %d)",
		      ptr,
		      *(unsigned long *)(mrr + 1),
		      *(unsigned long *)read_contents,
		      size);

	finish_this_record(&logfile);
#else
	VG_(memcpy)(read_contents, ptr, size);
#endif
}

static void
store_event(void *ptr, unsigned size, const void *written_bytes)
{
#if SEARCH_USES_MEMORY
	struct mem_write_record *mwr;
	struct record_header *rh;
	int safe;
#endif

	DEBUG(DBG_EVENTS, "store_event(%p, %x, %lx)\n", ptr, size,
	      *(unsigned long *)written_bytes & ((1 << (size * 8)) - 1) );

	if (access_is_magic(ptr, size))
		VG_(printf)("Thread %d storing %d (%lx) to %p (%lx)\n",
			    current_thread->id,
			    size,
			    *(unsigned long *)written_bytes,
			    ptr,
			    *(unsigned long *)ptr);

	if (RESCHEDULE_ON_EVERY_MEMORY_ACCESS ||
	    racetrack_address_races((Addr)ptr, size))
		reschedule_client(False, "store %d to %p (%lx -> %lx)", size, ptr,
				  *(unsigned long *)ptr,
				  *(unsigned long *)written_bytes);
	racetrack_write_region((Addr)ptr, size, current_thread->id);
	if (access_is_magic(ptr, size))
		VG_(printf)("Thread %d doing store %d (%lx) to %p (%lx)\n",
			    current_thread->id,
			    size,
			    *(unsigned long *)written_bytes,
			    ptr,
			    *(unsigned long *)ptr);

#if SEARCH_USES_MEMORY
	mwr = get_record_this_thread(&rh);

	replay_assert(rh->cls == RECORD_mem_write,
		      "wanted a memory write record in thread %d, got class %d",
		      current_thread->id,
		      rh->cls);
	replay_assert(ptr == mwr->ptr,
		      "wanted a write to %p, got one to %p",
		      mwr->ptr,
		      ptr);
	replay_assert(size == rh->size - sizeof(*rh) - sizeof(*mwr),
		      "wanted a write size %d, got one size %d",
		      rh->size - sizeof(*rh) - sizeof(*mwr),
		      size);

	VG_(memcpy)(ptr, written_bytes, size);

	safe = 1;
	if (VG_(memcmp)(written_bytes, mwr + 1, size)) {
		safe = 0;
		if ((size == 4 && *(unsigned *)written_bytes == NONDETERMINISM_POISON) ||
		    (size == 8 && *(unsigned long *)written_bytes == NONDETERMINISM_POISON))
			safe = 1;
	}
	replay_assert(safe,
		      "memory write divergence at address %p: wanted %lx but got %lx (size %d)",
		      ptr,
		      *(unsigned long *)(mwr + 1),
		      *(unsigned long *)written_bytes,
		      size);

	finish_this_record(&logfile);
#else
	VG_(memcpy)(ptr, written_bytes, size);
#endif
}

#define included_for_replay
#include "transform_expr.c"

void
new_race_address(Addr addr)
{
	unsigned code = SEARCH_CODE_NEW_RACE_ADDR;
	VG_(write)(worker_process_output_fd, &code, sizeof(code));
	VG_(write)(worker_process_output_fd, &addr, sizeof(addr));
}

static long
my_fork(void)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_fork));
	return res;
}

/* Take a snapshot of the current state, so that when we fail we only
   need to revert to here and not all the way back to the beginning of
   the run. */
/* The implementaion is moderately skanky.  This function never
   returns in the calling process, but instead sits and loops
   constantly forking off new worker processes which return and then
   go and do the actual exploration. */
void
exploration_take_snapshot(const Char *schedule)
{
	long child;
	unsigned code;
	Bool need_reset;
	int fds[2];

	need_reset = False;
	while (1) {
		VG_(pipe)(fds);
		child = my_fork();
		if (child == 0) {
			/* Go and do some work. */
			VG_(close)(fds[0]);
			worker_process_output_fd = fds[1];
			VG_(lseek)(logfile.fd,
				   logfile.offset_in_file,
				   VKI_SEEK_SET);
			return;
		}
		VG_(close)(fds[1]);

		/* We're the parent.  See how far that child gets. */
		do {
			if (VG_(read)(fds[0], &code, sizeof(code)) !=
			    sizeof(code)) {
				VG_(printf)("Child exitted unexpectedly.\n");
				my__exit(1);
			}

			switch (code) {
			case  SEARCH_CODE_REPLAY_SUCCESS:
				replay_run_finished(SEARCH_CODE_REPLAY_SUCCESS);

			case SEARCH_CODE_NEW_RACE_ADDR: {
				/* Proxy the results up the parent,
				   and then get out. */
				Addr addr;
				need_reset = True;
				VG_(read)(fds[0], &addr, sizeof(addr));
				VG_(write)(worker_process_output_fd,
					   &code,
					   sizeof(code));
				VG_(write)(worker_process_output_fd,
					   &addr,
					   sizeof(addr));
				break;
			}

			case SEARCH_CODE_REPLAY_FAILURE:
				if (need_reset) {
					/* Only the root driver can
					   handle a schedule reset.
					   Get out and let it deal
					   with it. */
					replay_run_finished(SEARCH_CODE_REPLAY_FAILURE);
				}
				break;

			default:
				VG_(printf)("Search worker process gave back unexpected code %x\n",
					    code);
				my__exit(1);
			}
		} while (code != SEARCH_CODE_REPLAY_FAILURE);

		/* That schedule didn't work.  Try another one. */
		VG_(close)(fds[0]);
		if (!advance_schedule_to_next_choice(schedule,
						     execution_schedule.file_size)) {
			/* Okay, we've failed.  The bad choice must
			   have happened before we were forked.  Let
			   the parent deal with it. */
			replay_run_finished(SEARCH_CODE_REPLAY_FAILURE);
		}
	}
}

/* The main driver loop.  This forks a series of worker processes.
   Each worker process will return, but in the driver itself this
   function loops forever. */
static void
driver_loop(const Char *schedule)
{
	long child;
	unsigned code;
	Bool need_schedule_reset;
	int fds[2];

	need_schedule_reset = True;
	while (1) {
		if (need_schedule_reset) {
			VG_(printf)("Resetting execution schedule.\n");
			create_empty_execution_schedule(schedule);
			need_schedule_reset = False;
		}

		VG_(pipe)(fds);
		child = my_fork();
		if (child == 0) {
			/* We're the child process, and so we need to
			   go and do the exploration. */
			VG_(close)(fds[0]);
			worker_process_output_fd = fds[1];
			return;
		}
		VG_(close)(fds[1]);

		/* We're the parent.  See how far that child gets. */
		do {
			if (VG_(read)(fds[0], &code, sizeof(code)) !=
			    sizeof(code)) {
				VG_(printf)("Child exitted unexpectedly.\n");
				my__exit(1);
			}

			switch (code) {
			case  SEARCH_CODE_REPLAY_SUCCESS:
				/* Child said that everything's okay.
				 * Woohoo. */
				VG_(printf)("Found a valid schedule.\n");
				my__exit(0);

			case SEARCH_CODE_NEW_RACE_ADDR: {
				/* The worker found a new racing
				   address.  Add it to the race table.
				   Need to reset the schedule when
				   this happens, because we don't know
				   what accesses there were to the
				   racing address before we discovered
				   it to be racy. */
				Addr addr;
				need_schedule_reset = True;
				VG_(read)(fds[0], &addr, sizeof(addr));
				VG_(printf)("Discovered race address %lx\n", addr);
				mark_address_as_racy(addr);
				break;
			}

			case SEARCH_CODE_REPLAY_FAILURE:
				/* Nothing to do */
				break;

			default:
				VG_(printf)("Search worker process gave back unexpected code %x\n",
					    code);
				my__exit(1);
			}
		} while (code != SEARCH_CODE_REPLAY_FAILURE);

		/* That schedule didn't work.  Try another one. */
		VG_(close)(fds[0]);
		if (!advance_schedule_to_next_choice(schedule, 0))
			VG_(tool_panic)((Char *)"Ran out of non-deterministic choices!");
	}
}

static Bool
client_request_event(ThreadId tid, UWord *arg_block, UWord *ret)
{
	struct record_header *rh;
	struct client_req_record *cr;

	if (!VG_IS_TOOL_USERREQ('P', 'P', arg_block[0]))
		return False;
	cr = get_record_this_thread(&rh);
	replay_assert(rh->cls == RECORD_client,
		      "wanted a client request record, got class %d (%s)",
		      rh->cls,
		      (const char *)arg_block[1]);
	replay_assert(cr->flavour == arg_block[0],
		      "wanted client request %x, got CR %x (%s)",
		      cr->flavour,
		      arg_block[0],
		      (const char *)arg_block[1]);
	finish_this_record(&logfile);
	*ret = 0;
	return True;
}

static void
init(void)
{
	const Char *schedule = (const Char *)"discovered_schedule";

	driver_loop(schedule);

	current_thread = VG_(malloc)("head_thread", sizeof(*current_thread));
	VG_(memset)(current_thread, 0, sizeof(*current_thread));
	current_thread->id = 1;
	current_thread->run_state = trs_running;

	VG_(printf)("Running search phase.\n");
	open_logfile(&logfile, (signed char *)"logfile1");

	open_execution_schedule(&execution_schedule, schedule);

	initialise_coroutine(&current_thread->coroutine, "head thread");

	/* Run the state machine.  It should come back here to get the
	   first instruction of the program executed. */
	VG_(printf)("Invoking replay state machine.\n");
	head_thread = current_thread;
#if 0
	in_monitor = True;
	run_coroutine(&head_thread->coroutine, &replay_state_machine,
		      "start of day");
	VG_(printf)("Replay state machine activated client.\n");
#endif
	VG_(running_tid) = VG_INVALID_THREADID;
}

static void
fini(Int ignore)
{
	VG_(printf)("Huh? Didn't expect fini() to get called.\n");
}

void
hit_end_of_log(void)
{
	unsigned code;
	struct replay_thread *rt;
	Bool anything_failed;
	int rv;

	close_logfile(&logfile);

	VG_(printf)("Hit end of log.\n");
	anything_failed = False;
	for (rt = head_thread; rt && !anything_failed; rt = rt->next_thread)
		anything_failed |= rt->run_state == trs_failed;

	if (anything_failed) {
		VG_(printf)("But some threads had failed, so the entire replay fails\n");
		code = SEARCH_CODE_REPLAY_FAILURE;
		rv = 1;
	} else {
		VG_(printf)("Finished search phase.\n");
		code = SEARCH_CODE_REPLAY_SUCCESS;
		rv = 0;
	}
	VG_(write)(worker_process_output_fd, &code, sizeof(code));
	my__exit(rv);
}

static ULong
rdtsc_event(void)
{
	struct rdtsc_record *rr;
	struct record_header *rh;
	ULong res;

	DEBUG(DBG_EVENTS, "rdtsc_event()\n");

	reschedule_client(False, "rdtsc");

	rr = get_record_this_thread(&rh);
	replay_assert(rh->cls == RECORD_rdtsc,
		      "wanted a rdtsc, got class %d",
		      rh->cls);
	res = rr->stashed_tsc;
	finish_this_record(&logfile);
	return res;
}

static void
new_thread_starting(void)
{
	VG_(printf)("New thread starting, in gen %d.\n",
		    VG_(in_generated_code));
	if (current_thread->id != 1) {
		current_thread->id = VG_(get_running_tid)();
		tl_assert(!current_thread->next_thread);
		current_thread->next_thread = head_thread;
		head_thread = current_thread;

		/* Anything written by the parent thread before the
		   child thread starts can be accessed by the child
		   without causing a race.  Let the race tracker know
		   about that. */
		racetrack_thread_message(current_thread->parent_id,
					 current_thread->id);

		reschedule_client(True, "immediately post spawn");
	}
}

static Long
replay_clone_syscall(Word (*fn)(void *),
		     void* stack,
		     Long  flags,
		     void* arg,
		     Long* child_tid,
		     Long* parent_tid,
		     vki_modify_ldt_t *foo)
{
	struct replay_thread *rt;

	VG_(printf)("Clone syscall\n");
	rt = VG_(malloc)("child thread", sizeof(*rt));
	VG_(memset)(rt, 0, sizeof(*rt));
	rt->run_state = trs_runnable;
	rt->parent_id = current_thread->id;
	make_coroutine(&rt->coroutine,
		       "child client thread",
		       stack,
		       0,
		       fn,
		       1,
		       arg);

	VG_(printf)("Currently in thread %d, gen %d\n", VG_(running_tid),
		    VG_(in_generated_code));
	VG_(running_tid) = VG_INVALID_THREADID;
	tl_assert(VG_(in_generated_code));
	VG_(in_generated_code) = False;
	switch_thread_client(rt, "newly spawning thread");
	VG_(printf)("Back in parent (%d, %d)\n", VG_(running_tid),
		    VG_(in_generated_code));
	VG_(in_generated_code) = True;

	return 52;
}

static void
pre_clo_init(void)
{
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
