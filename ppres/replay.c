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
#include "pub_tool_libcfile.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_amd64.h"
#include "libvex_trc_values.h"

#include "ppres.h"
#include "replay.h"
#include "coroutines.h"
#include "schedule.h"
#include "races.h"
#include "list.h"

/* Can the replay system see footstep records at all? */
#define SEARCH_USES_FOOTSTEPS 0
/* Use footsteps to explicitly choose which way to go (as opposed to
   just validating our decisions).  This forces a total ordering
   on all instructions. */
#define FOOTSTEP_DIRECTS_SEARCH 0

/* Restrict the search process to only see every nth memory access. */
#define SEARCH_SEES_EVERY_NTH_MEMORY_ACCESS 1

/* Use memory records to decide which thread to run.  This forces
   a total ordering on all memory accesses. */
#define MEMORY_DIRECTS_SEARCH 0

/* Setting this makes us reschedule on every memory access, rather
   than just the ones which might be racy. */
#define RESCHEDULE_ON_EVERY_MEMORY_ACCESS 0

/* We only use the global order for every nth access.  This is done by
   preventing threads from running if they have more than N memory
   accesses outstanding. */
#define ORDER_EVERY_NTH_MEMORY_ACCESS 50


/* Debug aid: log every memory access to this virtual address. */
#define MAGIC_ADDRESS ((void *)0x4220508)

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

#if SEARCH_USES_FOOTSTEPS && !FOOTSTEP_DIRECTS_SEARCH
/* Footsteps don't necessarily replay completely in global order, but
   we do require that they replay in order in each thread.  We
   therefore need to do a bit of buffering, to allow for the replay
   getting ahead of the log and vice versa. */
MK_SLIST_FUNCS(struct footstep_record, pfq)
static void validate_fr(const struct footstep_record *reference,
			const struct footstep_record *observed,
			ThreadId tid);
MK_ZIPPER_LIST(struct footstep_record, pfq, validate_fr)
#endif

#if !MEMORY_DIRECTS_SEARCH
/* Similar argument to footsteps: if we're not forcing memory accesses
   to have the same global order as they had in the record phase, we
   need some way of buffering them up per-thread so that we can
   validate them.  These lists provide that way. */
MK_SLIST_FUNCS(struct mem_access_event, mae)
static void validate_mem_access(const struct mem_access_event *recorded,
				const struct mem_access_event *observed,
				ThreadId tid);
MK_ZIPPER_LIST(struct mem_access_event, mae, validate_mem_access)
#endif

struct replay_thread {
	struct replay_thread *next_thread;
	struct coroutine coroutine;
	ThreadId id;
	Bool in_generated;
	Bool blocked;
	Bool failed;
#if SEARCH_USES_FOOTSTEPS && !FOOTSTEP_DIRECTS_SEARCH
	struct zipper_list_pfq pending_footsteps;
#endif
#if !MEMORY_DIRECTS_SEARCH
	struct zipper_list_mae pending_memory;
#endif
};

static struct coroutine
replay_state_machine;
static struct replay_thread *
head_thread, *
current_thread;
static struct execution_schedule
execution_schedule;
static int
worker_process_output_fd;
static int
in_monitor;
static struct replay_thread *
spawning_thread;

#define SEARCH_CODE_REPLAY_SUCCESS 0xa2b3c4d5
#define SEARCH_CODE_REPLAY_FAILURE 0xa2b3c4d6
#define SEARCH_CODE_NEW_RACE_ADDR 0xa2b3c4d7

static struct {
	enum {CLIENT_STOP_footstep = 12345,
	      CLIENT_STOP_syscall,
	      CLIENT_STOP_rdtsc,
	      CLIENT_STOP_mem_access,
	      CLIENT_STOP_ctxt_switch } cls;
	VexGuestAMD64State *state;
	union {
		struct mem_access_event mem;
		struct footstep_record footstep;
		struct replay_thread *ctxt_switch;
	} u;
} client_stop_reason;

static inline Word
syscall_sysnr(void)
{
	return client_stop_reason.state->guest_RAX;
}

static inline Word
syscall_arg_1(void)
{
	return client_stop_reason.state->guest_RDI;
}

static inline Word
syscall_arg_2(void)
{
	return client_stop_reason.state->guest_RSI;
}

static inline Word
syscall_arg_3(void)
{
	return client_stop_reason.state->guest_RDX;
}

static inline Word
syscall_arg_4(void)
{
	return client_stop_reason.state->guest_RCX;
}


static struct {
	unsigned long rdtsc;
} client_resume;

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


/* Switch from the client back to the monitor, remaining in the same
   thread. */
static void
run_replay_machine(void)
{
	struct replay_thread *whom;

	tl_assert(!in_monitor);
	whom = current_thread;
	run_coroutine(&whom->coroutine, &replay_state_machine,
		      "run_replay_machine");
	tl_assert(!in_monitor);
	tl_assert(current_thread == whom);
}

/* Switch to a different thread when we're in the monitor. */
static void
_switch_thread_monitor(struct replay_thread *target, const char *msg,
		       va_list args)
{
	tl_assert(in_monitor);
	tl_assert(current_thread != target);

	VG_(printf)("Monitor ctxt switch %d -> %d for ",
		    current_thread->id, target->id);
	VG_(vprintf)(msg, args);
	VG_(printf)("\n");

	current_thread->in_generated = VG_(in_generated_code);
	current_thread = target;
	VG_(in_generated_code) = current_thread->in_generated;
	VG_(running_tid) = current_thread->id;
}

static void
switch_thread_monitor(struct replay_thread *target, const char *msg,
		      ...)
{
	va_list args;
	va_start(args, msg);
	_switch_thread_monitor(target, msg, args);
	va_end(args);
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

	tl_assert(!in_monitor);
	tl_assert(target != current_thread);
	client_stop_reason.cls = CLIENT_STOP_ctxt_switch;
	client_stop_reason.u.ctxt_switch = target;

	VG_(printf)("Client ctxt switch %d -> %d for ",
		    current_thread->id, target->id);
	VG_(vprintf)(msg, args);
	VG_(printf)("\n");

	run_replay_machine();
	tl_assert(current_thread == me);
}

/* Run code from client @who for a bit, performing a context switch if
   necessary. */
static void
run_client(struct replay_thread *who, const char *msg, ...)
{
	va_list args;

	tl_assert(in_monitor);

	if (who != current_thread) {
		va_start(args, msg);
		_switch_thread_monitor(who, msg, args);
		va_end(args);
	}

	in_monitor = False;
	run_coroutine(&replay_state_machine, &who->coroutine,
		      "run_client");
	tl_assert(!in_monitor);
	in_monitor = True;

	while (client_stop_reason.cls == CLIENT_STOP_ctxt_switch) {
		switch_thread_monitor(client_stop_reason.u.ctxt_switch,
				      "requested by client %d",
				      current_thread->id);
		in_monitor = False;
		run_coroutine(&replay_state_machine,
			      &current_thread->coroutine,
			      "run_client after cswitch");
		in_monitor = True;
	}
}

static Bool
thread_runnable(const struct replay_thread *tr)
{
	const struct replay_thread *other_thread;

	if (tr->blocked)
		return False;
	tl_assert(!tr->failed); /* failed threads are always blocked */
#if !MEMORY_DIRECTS_SEARCH
	/* Try not to let threads get too far ahead of the log */
	if (!tr->pending_memory.pending_are_from_A &&
	    tr->pending_memory.pending.length >= ORDER_EVERY_NTH_MEMORY_ACCESS) {
		/* But if there's nothing else to run, we don't have
		 * any choice. */
		for (other_thread = head_thread;
		     other_thread;
		     other_thread = other_thread->next_thread) {
			if (other_thread->blocked)
				continue;
			if (!other_thread->pending_memory.pending_are_from_A &&
			    other_thread->pending_memory.pending.length >= ORDER_EVERY_NTH_MEMORY_ACCESS)
				continue;
			/* We could run other_thread instead, so
			   shouldn't choose tr */
			return False;
		}
		/* No choice: we have to run this thread, even though
		 * it's getting ahead. */
	}
#endif
	return True;
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
		if (current_thread->failed || current_thread->blocked) {
			/* Every thread is either failed or blocked,
			   so we can't continue.  Tell the monitor
			   that we're dead. */
			VG_(printf)("Ran out of threads to run.\n");
			replay_run_finished(SEARCH_CODE_REPLAY_FAILURE);
		}
		tl_assert(thread_runnable(current_thread));
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
	tl_assert(!rt->blocked);
	tl_assert(!rt->failed);
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

	tl_assert(!in_monitor);

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

/* Pick another thread to run.  This returns immediately with
   current_thread == the new thread (which might be the old one). */
static void
reschedule_monitor(Bool loud, const char *msg, ...)
{
	struct replay_thread *rt;
	va_list args;

	tl_assert(in_monitor);

	rt = select_new_thread();
	va_start(args, msg);
	if (rt == current_thread) {
		if (loud) {
			VG_(printf)("Monitor: keep in thread %d for ",
				    current_thread->id);
			VG_(vprintf)(msg, args);
			VG_(printf)("\n");
		}
	} else {
		_switch_thread_monitor(rt, msg, args);
	}
	va_end(args);
}

/* This thread has failed a validation, and so shouldn't be run any
   further. */
/* The semantics depend on whether you're in the monitor.  In the
   monitor, we pick another thread and return.  In client code, this
   function immediately schedules out and never returns. */
static void
failure(const char *fmt, ...)
{
	va_list args;

	VG_(printf)("Replay failed after %ld bytes\n",
		    logfile.offset_in_file);
	va_start(args, fmt);
	VG_(vprintf)(fmt, args);
	va_end(args);

	execution_schedule.failed = True;

	/* Mark this thread as failed, but let every other thread
	   carry on, so that we have a better chance of finding
	   interesting races. */
	current_thread->failed = True;
	current_thread->blocked = True;
	if (in_monitor) {
		reschedule_monitor(True, "thread failed");
	} else {
		reschedule_client(True, "thread failed");
		VG_(tool_panic)((Char *)"Running a failed thread!");
	}
}

/* This does not behave like you would expect, so gets an XXX. */
#define replay_assert_XXX(cond, msg, ...)                 \
do {                                                      \
	if (!(cond)) {					  \
		failure("Assertion %s failed at %d: " msg "\n", \
                        #cond , __LINE__, ## __VA_ARGS__);		\
                if (in_monitor)                           \
			finish_this_record(&logfile);	  \
                return;                                   \
        }                                                 \
} while (0)

#define replay_assert_XXX_no_finish(cond, msg, ...)       \
do {                                                      \
	if (!(cond)) {					  \
		failure("Assertion %s failed at %d: " msg "\n", \
                        #cond , __LINE__, ## __VA_ARGS__);\
                return;                                   \
        }                                                 \
} while (0)

#if SEARCH_USES_FOOTSTEPS
static void
validate_fr(const struct footstep_record *reference,
	    const struct footstep_record *observed,
	    ThreadId tid)
{
	replay_assert_XXX_no_finish(reference->rip == observed->rip,
				    "wanted a footstep at %lx, got one at %lx",
				    reference->rip,
				    observed->rip);
	replay_assert_XXX_no_finish(reference->rax == observed->rax, "RAX mismatch: %lx != %lx",
				    reference->rax, observed->rax);
	replay_assert_XXX_no_finish(reference->rdx == observed->rdx, "RDX mismatch");
	replay_assert_XXX_no_finish(reference->rcx == observed->rcx ||
				    observed->rcx == NONDETERMINISM_POISON,
				    "RCX mismatch");
}

static void
capture_footstep_record(struct footstep_record *fr,
			VexGuestAMD64State *state)
{
	fr->rip = state->guest_RIP;
	fr->rax = state->guest_RAX;
	fr->rdx = state->guest_RDX;
	fr->rcx = state->guest_RCX;
}

static void
footstep_event(VexGuestAMD64State *state, Addr rip)
{
#if FOOTSTEP_DIRECTS_SEARCH
	reschedule_client(False, "footstep at %lx\n", rip);
	state->guest_RIP = rip;
	client_stop_reason.cls = CLIENT_STOP_footstep;
	client_stop_reason.state = state;
	capture_footstep_record(&client_stop_reason.u.footstep, state);
	run_replay_machine();
#else
	struct footstep_record current_fr;
	state->guest_RIP = rip;
	capture_footstep_record(&current_fr, state);
	zipper_add_B_pfq(&current_thread->pending_footsteps,
			 current_fr, current_thread->id);
#endif
}
#endif

static void
syscall_event(VexGuestAMD64State *state)
{
	reschedule_client(False, "syscall %d", state->guest_RAX);
	client_stop_reason.cls = CLIENT_STOP_syscall;
	client_stop_reason.state = state;
	run_replay_machine();
}

static void
replay_load(const void *ptr, unsigned size, void *read_contents)
{
	struct mem_access_event mae;

	if (ptr == MAGIC_ADDRESS)
		VG_(printf)("Thread %d load %d from %p\n",
			    current_thread->id,
			    size,
			    ptr);

	if (RESCHEDULE_ON_EVERY_MEMORY_ACCESS ||
	    racetrack_address_races((Addr)ptr, size))
		reschedule_client(False, "load %d from %p", size, ptr);

	racetrack_read_region((Addr)ptr, size, current_thread->id);
	VG_(memcpy)(read_contents, ptr, size);

	if (ptr == MAGIC_ADDRESS)
		VG_(printf)("Thread %d did load %d from %p -> %lx\n",
			    current_thread->id,
			    size,
			    ptr,
			    *(unsigned long *)ptr);

	mae.is_read = True;
	mae.ptr = (void *)ptr;
	mae.size = size;
	VG_(memcpy)(mae.buffer, read_contents, size);

#if MEMORY_DIRECTS_SEARCH
	client_stop_reason.cls = CLIENT_STOP_mem_access;
	client_stop_reason.u.mem = mae;
	run_replay_machine();
#else
	zipper_add_B_mae(&current_thread->pending_memory, mae,
			 current_thread->id);
#endif
}

static void
replay_store(void *ptr, unsigned size, const void *written_bytes)
{
	struct mem_access_event mae;

	if (ptr == MAGIC_ADDRESS)
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
	if (ptr == MAGIC_ADDRESS)
		VG_(printf)("Thread %d doing store %d (%lx) to %p (%lx)\n",
			    current_thread->id,
			    size,
			    *(unsigned long *)written_bytes,
			    ptr,
			    *(unsigned long *)ptr);

	VG_(memcpy)(ptr, written_bytes, size);

	mae.is_read = False;
	mae.ptr = (void *)ptr;
	mae.size = size;
	VG_(memcpy)(mae.buffer, written_bytes, size);

#if MEMORY_DIRECTS_SEARCH
	client_stop_reason.cls = CLIENT_STOP_mem_access;
	client_stop_reason.u.mem = mae;
	run_replay_machine();
#else
	zipper_add_B_mae(&current_thread->pending_memory, mae,
			 current_thread->id);
#endif
}

#define included_for_replay
#include "transform_expr.c"

static struct replay_thread *
get_thread(ThreadId id)
{
	struct replay_thread *rt;

	for (rt = head_thread; rt && rt->id != id; rt = rt->next_thread)
		;
	tl_assert(rt != NULL);
	return rt;
}

void
new_race_address(Addr addr)
{
	unsigned code = SEARCH_CODE_NEW_RACE_ADDR;
	VG_(write)(worker_process_output_fd, &code, sizeof(code));
	VG_(write)(worker_process_output_fd, &addr, sizeof(addr));
}

static void
replay_footstep_record(struct footstep_record *fr,
		       struct record_header *rh)
{
#if SEARCH_USES_FOOTSTEPS
#if FOOTSTEP_DIRECTS_SEARCH
	run_client(get_thread(rh->tid), "forced by footstep record");
	replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_footstep,
			  "expected a footstep, got class %d",
			  client_stop_reason.cls);
	validate_fr(fr, &client_stop_reason.u.footstep, rh->tid);
#else
 	zipper_add_A_pfq(&get_thread(rh->tid)->pending_footsteps,
 			 *fr, rh->tid);
#endif
#endif
	finish_this_record(&logfile);
}

static void
replay_memory_record(struct record_header *rh,
		     struct memory_record *mr)
{
	VG_(memcpy)(mr->ptr,
		    mr + 1,
		    rh->size - sizeof(*rh) - sizeof(*mr));
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
replay_syscall_record(struct record_header *rh,
		      struct syscall_record *sr)
{
	run_client(current_thread, "syscall record");

	replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_syscall &&
			  rh->tid == current_thread->id,
			  "wanted a syscall %d in thread %d, got class %d (%d) in thread %d",
			  sr->syscall_nr,
			  rh->tid,
			  client_stop_reason.cls,
			  client_stop_reason.state->guest_RAX,
			  current_thread->id);
	replay_assert_XXX(client_stop_reason.state->guest_RAX == sr->syscall_nr,
			  "wanted syscall %d, got syscall %ld",
			  sr->syscall_nr,
			  client_stop_reason.state->guest_RAX);

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
	case __NR_exit_group:
	case __NR_exit:

	case __NR_nanosleep: /* XXX: We should arguably tweak the
				scheduler to prefer not to select this
				thread when we see one of these.
				Maybe later. */

	case __NR_write: /* Should maybe do something special with
			    these so that we see stuff on stdout? */

		if (sr_isError(sr->syscall_res))
			client_stop_reason.state->guest_RAX = -sr_Err(sr->syscall_res);
		else
			client_stop_reason.state->guest_RAX = sr_Res(sr->syscall_res);
		finish_this_record(&logfile);
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
			replay_assert_XXX(-client_stop_reason.state->guest_RAX ==
					  sr_Err(sr->syscall_res),
					  "Expected syscall to fail %d, actually got %d",
					  sr_Err(sr->syscall_res),
					  -client_stop_reason.state->guest_RAX);
		else
			replay_assert_XXX(client_stop_reason.state->guest_RAX ==
					  sr_Res(sr->syscall_res),
					  "expected syscall to succeed %d, actually got %d",
					  sr_Res(sr->syscall_res),
					  client_stop_reason.state->guest_RAX);
		finish_this_record(&logfile);
		break;

		/* Bizarre calling convention: returns the PID, so we need
		   to run the call and then shove the results in. */
	case __NR_set_tid_address:
		if (sr_isError(sr->syscall_res)) {
			client_stop_reason.state->guest_RAX = -sr_Err(sr->syscall_res);
		} else {
			VG_(client_syscall)(VG_(get_running_tid)(),
					    VEX_TRC_JMP_SYS_SYSCALL);
			client_stop_reason.state->guest_RAX = sr_Res(sr->syscall_res);
		}
		finish_this_record(&logfile);
		break;

	case __NR_clone:
		/* This is a bit awkward.  First, we need to manually
		   advance RIP over the syscall instruction, for
		   reasons which aren't particularly clear. */
		client_stop_reason.state->guest_RIP += 2;
		if (sr_isError(sr->syscall_res)) {
			client_stop_reason.state->guest_RAX = -sr_Err(sr->syscall_res);
		} else {
			/* Now we need to issue the clone syscall
			   itself.  This won't actually do a syscall
			   at the kernel level, because it'll get
			   trapped in replay_clone_syscall() and
			   turned into the creation of a
			   replay_thread. */
			VG_(client_syscall)(VG_(get_running_tid)(),
					    VEX_TRC_JMP_SYS_SYSCALL);
			tl_assert(spawning_thread != NULL);
			client_stop_reason.state->guest_RAX = sr_Res(sr->syscall_res);

			/* And now we need to consider running the
			   child.  Linux seems to slightly prefer
			   running the child before running the
			   parent, so do the same thing. */
			switch_thread_monitor(spawning_thread, "run newly spawned thread");
			spawning_thread = NULL;
			reschedule_monitor(False, "immediately post clone");
		}
		finish_this_record(&logfile);
		break;

	case __NR_mmap: {
		Addr addr;
		ULong length;
		SysRes map_res;
		Word prot;

		if (sr_isError(sr->syscall_res)) {
			client_stop_reason.state->guest_RAX = -sr_Err(sr->syscall_res);
			finish_this_record(&logfile);
			break;
		}
		addr = sr_Res(sr->syscall_res);
		length = client_stop_reason.state->guest_RSI;
		prot = client_stop_reason.state->guest_RDX;
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
		client_stop_reason.state->guest_RAX = addr;
		break;
	}

	case __NR_futex:
		/* Don't need to do anything here: we have explicit
		   block/unblock records which tell us exactly what to
		   do. */
		if (sr_isError(sr->syscall_res))
			client_stop_reason.state->guest_RAX = -sr_Err(sr->syscall_res);
		else
			client_stop_reason.state->guest_RAX = sr_Res(sr->syscall_res);
		finish_this_record(&logfile);
		break;

	default:
		VG_(printf)("don't know how to replay syscall %lld yet\n",
			    client_stop_reason.state->guest_RAX);
		VG_(exit)(1);
	}
}

static void
replay_rdtsc_record(struct rdtsc_record *rr)
{
	run_client(current_thread, "rdtsc record");

	replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_rdtsc,
			  "wanted a rdtsc, got class %d",
			  client_stop_reason.cls);
	client_resume.rdtsc = rr->stashed_tsc;

	finish_this_record(&logfile);
}

static int mem_access_counter;

static void
validate_mem_access(const struct mem_access_event *recorded,
		    const struct mem_access_event *observed,
		    ThreadId tid)
{
	int safe;

	if (mem_access_counter++ % SEARCH_SEES_EVERY_NTH_MEMORY_ACCESS != 0)
		return;

	replay_assert_XXX_no_finish(observed->is_read == recorded->is_read,
				    "wrong memory type (%d, expected %d)",
				    observed->is_read, recorded->is_read);
	replay_assert_XXX_no_finish(observed->ptr == recorded->ptr,
				    "Expected an access from %p, got one from %p",
				    recorded->ptr, observed->ptr);
	replay_assert_XXX_no_finish(observed->size == recorded->size,
				    "wanted access of size %d, got size %d",
				    recorded->size, observed->size);
	safe = 1;
	if (VG_(memcmp)(observed->buffer, recorded->buffer, recorded->size)) {
		safe = 0;
		switch (recorded->size) {
		case 4:
			if (*(unsigned *)observed->buffer == NONDETERMINISM_POISON)
				safe = 1;
			break;
		case 8:
			if (*(unsigned long *)observed->buffer == NONDETERMINISM_POISON)
				safe = 1;
			break;
		}
	}
	if (!safe)
		failure("Memory divergence (read = %d) in thread %d at address %p; wanted %lx but got %lx (size %d)!\n",
			recorded->is_read,
			tid,
			recorded->ptr,
			*(unsigned long *)recorded->buffer,
			*(unsigned long *)observed->buffer,
			recorded->size);
}

static void
replay_mem_record(struct record_header *rh,
		  const struct mem_access_event *recorded)
{
#if MEMORY_DIRECTS_SEARCH
	run_client(get_thread(rh->tid), "forced by memory read");
	replay_assert_XXX(current_thread->id == rh->tid,
			  "wanted to be in thread %d, was in %d",
			  rh->tid,
			  current_thread->id);
	replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_mem_access,
			  "wanted a memory read, got class %d",
			  client_stop_reason.cls);
	validate_mem_access(recorded, &client_stop_reason.u.mem);
#else
	zipper_add_A_mae(&get_thread(rh->tid)->pending_memory,
			 *recorded, rh->tid);
#endif
	finish_this_record(&logfile);
}

static void
pre_process_mem_read(const struct mem_read_record *mrr,
		     const struct record_header *rh,
		     struct mem_access_event *mae)
{
	mae->is_read = True;
	mae->ptr = mrr->ptr;
	mae->size = rh->size - sizeof(*rh) - sizeof(*mrr);
	VG_(memcpy)(mae->buffer, mrr + 1, mae->size);
}

static void
pre_process_mem_write(const struct mem_write_record *mwr,
		      const struct record_header *rh,
		      struct mem_access_event *mae)
{
	mae->is_read = False;
	mae->ptr = mwr->ptr;
	mae->size = rh->size - sizeof(*rh) - sizeof(*mwr);
	VG_(memcpy)(mae->buffer, mwr + 1, mae->size);
}

static void
replay_mem_read_record(struct record_header *rh,
		       struct mem_read_record *mrr)
{
	struct mem_access_event mae;
	pre_process_mem_read(mrr, rh, &mae);
	replay_mem_record(rh, &mae);
}

static void
replay_mem_write_record(struct record_header *rh,
			struct mem_write_record *mwr)
{
	struct mem_access_event mae;
	pre_process_mem_write(mwr, rh, &mae);
	replay_mem_record(rh, &mae);
}

static void
block_thread(ThreadId id)
{
	struct replay_thread *rt = get_thread(id);
	rt->blocked = True;
	finish_this_record(&logfile);
	if (rt == current_thread)
		reschedule_monitor(True, "thread blocking");
}

static void
unblock_thread(ThreadId id)
{
	struct replay_thread *rt = get_thread(id);
	rt->blocked = False;
	finish_this_record(&logfile);
	reschedule_monitor(True, "thread unblocking");
}

static void
replay_state_machine_fn(void)
{
	struct record_header *rh;
	void *payload;

	VG_(printf)("Replay state machine starting...\n");
	if (VG_(running_tid) == 0)
		VG_(running_tid) = 1;
	while (1) {
		rh = get_current_record(&logfile);
		if (get_thread(rh->tid)->failed) {
			/* This record relates to a thread which has
			   already failed, so just throw it away. */
			finish_this_record(&logfile);
			continue;
		}

		payload = rh + 1;
		switch (rh->cls) {
		case RECORD_footstep:
			replay_footstep_record(payload, rh);
			break;
		case RECORD_syscall:
			replay_syscall_record(rh, payload);
			process_memory_records();
			break;
		case RECORD_memory:
			VG_(tool_panic)((signed char *)"Got a memory record not in a syscall record");
			break;
		case RECORD_rdtsc:
			replay_rdtsc_record(payload);
			break;
		case RECORD_mem_read:
			replay_mem_read_record(rh, payload);
			break;
		case RECORD_mem_write:
			replay_mem_write_record(rh, payload);
			break;
		case RECORD_new_thread:
			/* Don't actually need to do anything here:
			   we'll get a clone syscall record in a
			   second, and that's more useful. */
			finish_this_record(&logfile);
			break;
		case RECORD_thread_blocking:
			block_thread(rh->tid);
			break;
		case RECORD_thread_unblocked:
			unblock_thread(rh->tid);
			break;
		default:
			VG_(tool_panic)((signed char *)"Unknown replay record type!");
		}
	}
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

static void
init(void)
{
	static unsigned char replay_state_machine_stack[16384];
	const Char *schedule = (const Char *)"discovered_schedule";
	long child;
	int fds[2];
	unsigned code;
	Bool need_schedule_reset;

	/* Search for a valid execution schedule. */

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
			break;
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
		advance_schedule_to_next_choice(schedule);
	}

	make_coroutine(&replay_state_machine,
		       "replay_state_machine",
		       replay_state_machine_stack,
		       sizeof(replay_state_machine_stack),
		       replay_state_machine_fn,
		       0);

	head_thread = VG_(malloc)("head_thread", sizeof(*head_thread));
	VG_(memset)(head_thread, 0, sizeof(*head_thread));
	head_thread->id = 1;

	VG_(printf)("Running search phase.\n");
	open_logfile(&logfile, (signed char *)"logfile1");

	open_execution_schedule(&execution_schedule, schedule);

	/* Run the state machine.  It should come back here to get the
	   first instruction of the program executed. */
	VG_(printf)("Invoking replay state machine.\n");
	current_thread = head_thread;
	initialise_coroutine(&head_thread->coroutine, "head thread");
	in_monitor = True;
	run_coroutine(&head_thread->coroutine, &replay_state_machine,
		      "start of day");
	VG_(printf)("Replay state machine activated client.\n");
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
		anything_failed |= rt->failed;

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
replay_rdtsc(void)
{
	reschedule_client(False, "rdtsc");
	client_stop_reason.cls = CLIENT_STOP_rdtsc;
	run_replay_machine();
	return client_resume.rdtsc;
}

static void
new_thread_starting(void)
{
	if (spawning_thread) {
		VG_(printf)("New thread starting, in gen %d.\n",
			    VG_(in_generated_code));
		spawning_thread->id = VG_(get_running_tid)();
		run_replay_machine();
		VG_(printf)("New thread starting for real, in gen %d.\n",
			    VG_(in_generated_code));
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
	struct replay_thread *rt, *local_thread;

	VG_(printf)("Clone syscall\n");
	rt = VG_(malloc)("child thread", sizeof(*rt));
	VG_(memset)(rt, 0, sizeof(*rt));
	spawning_thread = rt;
	make_coroutine(&rt->coroutine,
		       "child client thread",
		       stack,
		       0,
		       fn,
		       1,
		       arg);

	VG_(printf)("Currently in thread %d\n", VG_(running_tid));
	local_thread = current_thread;
	run_client(spawning_thread, "newly spawning thread");

	rt->next_thread = head_thread;
	head_thread = rt;

	/* Valgrind requires us to be in the parent thread when this
	   returns, so get there now.  We'll insert a reschedule point
	   from the normal syscall handlers. */
	switch_thread_monitor(local_thread, "VG requires no thread switch during clone");

	return 52;
}

static void
pre_clo_init(void)
{
	VG_(tool_handles_synchronisation) = True;
	tool_provided_rdtsc = replay_rdtsc;
	VG_(tool_provided_thread_starting) = new_thread_starting;
	tool_provided_clone_syscall =
		replay_clone_syscall;

	VG_(details_name)((signed char *)"ppres_rep");
	VG_(details_version)((signed char *)"0.0");
	VG_(details_copyright_author)((signed char *)"Steven Smith");
	VG_(details_bug_reports_to)((signed char *)"sos22@cam.ac.uk");
	VG_(details_description)((signed char *)"Replayer for PPRES");
	VG_(basic_tool_funcs)(init, instrument_func, fini);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
