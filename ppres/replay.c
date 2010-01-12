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

/* Can the replay system see footstep records at all? */
#define SEARCH_USES_FOOTSTEPS 1
/* Use footsteps to explicitly choose which way to go (as opposed to
   just validating our decisions).  This forces a total ordering
   on all instructions. */
#define FOOTSTEP_DIRECTS_SEARCH 0

/* Restrict the search process to only see every nth memory access. */
#define SEARCH_SEES_EVERY_NTH_MEMORY_ACCESS 1
/* Use memory records to decide which thread to run.  This forces
   a total ordering on all memory accesses. */
#define MEMORY_DIRECTS_SEARCH 0

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

#if SEARCH_USES_FOOTSTEPS
/* Footsteps don't necessarily replay completely in global order, but
   we do require that they replay in order in each thread.  We
   therefore need to do a bit of buffering, to allow for the replay
   getting ahead of the log and vice versa. */
struct pending_footstep {
	struct pending_footstep *next;
	struct footstep_record fr;
};

struct pending_footstep_queue {
	struct pending_footstep *head;
	struct pending_footstep *tail;
};

struct pending_footstep_thread {
	struct pending_footstep_thread *next;
	ThreadId tid;

	/* pending_footsteps is either footsteps which have been seen
	   in the log (log_is_ahead_of_world is true) or which have
	   been seen in the replay (log_is_ahead_of_world is
	   false). */
	Bool log_is_ahead_of_world;
	struct pending_footstep_queue pending_footsteps;
};
#endif

struct replay_thread {
	struct replay_thread *next_thread;
	struct coroutine coroutine;
	ThreadId id;
	Bool in_generated;
	Bool blocked;
	Bool failed;
	struct pending_footstep_thread pending_footsteps;
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

#define SEARCH_CODE_REPLAY_SUCCESS 0xa2b3c4d5
#define SEARCH_CODE_REPLAY_FAILURE 0xa2b3c4d6
#define SEARCH_CODE_NEW_RACE_ADDR 0xa2b3c4d7

#define CSR_BUFFER 16

static struct {
	enum {CLIENT_STOP_footstep = 12345,
	      CLIENT_STOP_syscall,
	      CLIENT_STOP_rdtsc,
	      CLIENT_STOP_mem_read,
	      CLIENT_STOP_mem_write} cls;
	VexGuestAMD64State *state;
	union {
		struct {
			const void *ptr;
			unsigned size;
			unsigned char buffer[CSR_BUFFER];
		} mem_read;
		struct {
			void *ptr;
			unsigned size;
			unsigned char buffer[CSR_BUFFER];
		} mem_write;
		struct footstep_record footstep;
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


/* Switch from the monitor to client code in thread @who (which might
   be the current thread).  The client might do a thread switch
   itself, so we can be anywhere when we come back. */
static void
run_client(struct replay_thread *who, const char *msg, ...)
{
	va_list args;
	if (who != current_thread) {
		va_start(args, msg);
		VG_(printf)("Monitor goes to thread %d for ",
			    who->id);
		VG_(vprintf)(msg, args);
		VG_(printf)("\n");
		va_end(args);
	}

	current_thread->in_generated = VG_(in_generated_code);
	current_thread = who;

	in_monitor = False;
	run_coroutine(&replay_state_machine, &who->coroutine);
	in_monitor = True;
}

/* Switch from the client back to the monitor, remaining in the same
   thread.  The monitor might switch threads itself, but when this
   returns we'll be back where we started. */
static void
run_replay_machine(void)
{
	struct replay_thread *whom;

	whom = current_thread;
	current_thread->in_generated = VG_(in_generated_code);
	in_monitor = True;
	run_coroutine(&whom->coroutine, &replay_state_machine);
	in_monitor = False;
	tl_assert(current_thread == whom);
	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = current_thread->in_generated;
}

static void
reschedule_core(Bool loud, struct coroutine *my_coroutine, const char *msg, va_list args)
{
	struct replay_thread *rt, *me;
	unsigned other_threads;
	unsigned thread_to_run;
	unsigned x;
	unsigned code;

	me = current_thread;
	other_threads = 0;
	rt = head_thread;
	while (rt != NULL) {
		if (rt != me && !rt->blocked)
			other_threads++;
		rt = rt->next_thread;
	}

	if (other_threads == 0) {
		if (current_thread->failed || current_thread->blocked) {
			/* Every thread is either failed or blocked,
			   so we can't continue.  Tell the monitor
			   that we're dead. */
			VG_(printf)("Ran out of threads to run.\n");
			code = SEARCH_CODE_REPLAY_FAILURE;
			VG_(write)(worker_process_output_fd, &code, sizeof(code));
			my__exit(1);
		}
		tl_assert(!current_thread->blocked);
	}
	thread_to_run = make_nd_choice(&execution_schedule,
				       other_threads);
	tl_assert(thread_to_run <= other_threads);
	if (thread_to_run == 0 && !current_thread->blocked) {
		/* Keep running this thread. */
		if (loud) {
			VG_(printf)("Keep in thread %d for ",
				    current_thread->id);
			VG_(vprintf)(msg, args);
			VG_(printf)("\n");
		}
		return;
	}

	rt = head_thread;
	if (rt == me)
		rt = rt->next_thread;
	x = 1;
	while (x < thread_to_run) {
		rt = rt->next_thread;
		tl_assert(rt != NULL);
		while (rt == me || rt->blocked)
			rt = rt->next_thread;
		x++;
	}
	tl_assert(rt != NULL);
	tl_assert(rt != me);
	tl_assert(!rt->blocked);
	tl_assert(!rt->failed);

	VG_(printf)("Switch to thread %d for ", rt->id);
	VG_(vprintf)(msg, args);
	VG_(printf)("\n");

	me->in_generated = VG_(in_generated_code);
	current_thread = rt;
	in_monitor = False;
	run_coroutine(my_coroutine, &rt->coroutine);
	if (my_coroutine == &replay_state_machine)
		in_monitor = True;
	if (!me->blocked)
		current_thread = me;
	else
		VG_(printf)("Switch back again to %d\n", me->id);

	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = current_thread->in_generated;
}

static void
reschedule(Bool loud, const char *msg, ...)
{
	va_list args;
	va_start(args, msg);
	if (in_monitor)
		reschedule_core(loud, &replay_state_machine, msg, args);
	else
		reschedule_core(loud, &current_thread->coroutine, msg, args);
	va_end(args);

	tl_assert(!current_thread->blocked);
}

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
	reschedule(True, "thread failed");
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

#if SEARCH_USES_FOOTSTEPS
static void
validate_fr(const struct footstep_record *reference,
	    const struct footstep_record *observed)
{
	replay_assert_XXX(reference->rip == observed->rip,
			  "wanted a footstep at %lx, got one at %lx",
			  reference->rip,
			  observed->rip);
	replay_assert_XXX(reference->rax == observed->rax, "RAX mismatch: %lx != %lx",
			  reference->rax, observed->rax);
	replay_assert_XXX(reference->rdx == observed->rdx, "RDX mismatch");
	replay_assert_XXX(reference->rcx == observed->rcx ||
			  observed->rcx == NONDETERMINISM_POISON,
			  "RCX mismatch");
	if (in_monitor)
		finish_this_record(&logfile);
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

static Bool
pfq_empty(struct pending_footstep_queue *pfq)
{
	return pfq->head == NULL;
}

static void
push_pending_footstep(struct pending_footstep_queue *pfq,
		      struct footstep_record fr)
{
	struct pending_footstep *pf;

	pf = VG_(malloc)("pending footstep", sizeof(*pf));
	VG_(memset)(pf, 0, sizeof(*pf));
	pf->next = NULL;
	pf->fr = fr;
	if (pfq->tail)
		pfq->tail->next = pf;
	else
		pfq->head = pf;
	pfq->tail = pf;
}

static struct footstep_record
pop_pending_footstep(struct pending_footstep_queue *pfq)
{
	struct footstep_record res;
	struct pending_footstep *pf;

	pf = pfq->head;
	pfq->head = pf->next;
	if (pfq->tail == pf)
		pfq->tail = NULL;
	tl_assert(pf);
	res = pf->fr;
	VG_(free)(pf);
	return res;
}

static void
footstep_event(VexGuestAMD64State *state, Addr rip)
{
#if FOOTSTEP_DIRECTS_SEARCH
	reschedule(False, "footstep at %lx\n", rip);
	state->guest_RIP = rip;
	client_stop_reason.cls = CLIENT_STOP_footstep;
	client_stop_reason.state = state;
	capture_footstep_record(&client_stop_reason.u.footstep, state);
	run_replay_machine();
#else
	struct footstep_record current_fr;
	struct pending_footstep_thread *pft;
	struct footstep_record expected_fr;
	state->guest_RIP = rip;
	capture_footstep_record(&current_fr, state);
	pft = &current_thread->pending_footsteps;
	if (pfq_empty(&pft->pending_footsteps) ||
	    !pft->log_is_ahead_of_world) {
		pft->log_is_ahead_of_world = False;
		push_pending_footstep(&pft->pending_footsteps,
				      current_fr);
	} else {
		expected_fr = pop_pending_footstep(&pft->pending_footsteps);
		validate_fr(&current_fr, &expected_fr);
	}
#endif
}
#endif

static void
syscall_event(VexGuestAMD64State *state)
{
	reschedule(False, "syscall %d", state->guest_RAX);
	client_stop_reason.cls = CLIENT_STOP_syscall;
	client_stop_reason.state = state;
	run_replay_machine();
}

static void
replay_load(const void *ptr, unsigned size, void *read_contents)
{
	reschedule(False, "load %d from %p", size, ptr);

	racetrack_read_region((Addr)ptr, size, current_thread->id);
	VG_(memcpy)(read_contents, ptr, size);
	client_stop_reason.cls = CLIENT_STOP_mem_read;
	client_stop_reason.u.mem_read.ptr = ptr;
	client_stop_reason.u.mem_read.size = size;
	VG_(memcpy)(client_stop_reason.u.mem_read.buffer,
		    read_contents,
		    size);
	run_replay_machine();
}

static void
replay_store(void *ptr, unsigned size, const void *written_bytes)
{
	reschedule(False, "store %d to %p", size, ptr);

	racetrack_write_region((Addr)ptr, size, current_thread->id);
	VG_(memcpy)(ptr, written_bytes, size);
	client_stop_reason.cls = CLIENT_STOP_mem_write;
	client_stop_reason.u.mem_write.ptr = ptr;
	client_stop_reason.u.mem_write.size = size;
	VG_(memcpy)(client_stop_reason.u.mem_write.buffer,
		    written_bytes,
		    size);
	run_replay_machine();
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
	validate_fr(&client_stop_reason.u.footstep, fr);
#else
	struct pending_footstep_thread *pft = &get_thread(rh->tid)->pending_footsteps;
	struct footstep_record expected_fr;

	if (pfq_empty(&pft->pending_footsteps) ||
	    pft->log_is_ahead_of_world) {
		pft->log_is_ahead_of_world = True;
		push_pending_footstep(&pft->pending_footsteps, *fr);
		finish_this_record(&logfile);
	} else {
		expected_fr = pop_pending_footstep(&pft->pending_footsteps);
		validate_fr(fr, &expected_fr);
	}
#endif
#endif
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

	replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_syscall,
			  "wanted a syscall in thread %d, got class %d in thread %d",
			  rh->tid,
			  client_stop_reason.cls,
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

	case __NR_clone: /* XXX hmm... */
		client_stop_reason.state->guest_RIP += 2;

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

#define MAGIC_PTR (void *)0

static int mem_access_counter;

static void
replay_mem_read_record(struct record_header *rh,
		       struct mem_read_record *mrr)
{
	unsigned recorded_read_size;
	void *recorded_read;
	int safe;

#if MEMORY_DIRECTS_SEARCH
	run_client(get_thread(rh->tid), "forced by memory read");
#else
	run_client(current_thread, "memory read");
#endif

	if (mem_access_counter++ % SEARCH_SEES_EVERY_NTH_MEMORY_ACCESS == 0) {
		if (mrr->ptr == MAGIC_PTR)
			VG_(printf)("Thread %d(%d) reads %x\n",
				    current_thread->id,
				    rh->tid,
				    *(unsigned *)client_stop_reason.u.mem_read.buffer);

		replay_assert_XXX(current_thread->id == rh->tid,
				  "wanted to be in thread %d, was in %d",
				  rh->tid,
				  current_thread->id);
		replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_mem_read,
				  "wanted a memory read, got class %d",
				  client_stop_reason.cls);
		replay_assert_XXX(client_stop_reason.u.mem_read.ptr == mrr->ptr,
				  "Expected a read from %p, got one from %p",
				  mrr->ptr,
				  client_stop_reason.u.mem_read.ptr);

		recorded_read_size = rh->size - sizeof(*rh) - sizeof(*mrr);
		recorded_read = mrr + 1;
		replay_assert_XXX(client_stop_reason.u.mem_read.size == recorded_read_size,
				  "wanted read of size %d, got size %d",
				  recorded_read_size, client_stop_reason.u.mem_read.size);

		safe = 1;
		if (VG_(memcmp)(client_stop_reason.u.mem_read.buffer,
				recorded_read,
				recorded_read_size)) {
			safe = 0;
			switch (recorded_read_size) {
			case 4:
				if (*(unsigned *)client_stop_reason.u.mem_read.buffer ==
				    NONDETERMINISM_POISON)
					safe = 1;
				break;
			case 8:
				if (*(unsigned long *)client_stop_reason.u.mem_read.buffer ==
				    NONDETERMINISM_POISON)
					safe = 1;
				break;
			}
		}
		if (!safe)
			failure("Memory divergence (read) at address %p; wanted %lx but got %lx (size %d)!\n",
				mrr->ptr,
				*(unsigned long *)recorded_read,
				*(unsigned long *)mrr->ptr,
				recorded_read_size);
	}
	finish_this_record(&logfile);
}

static void
replay_mem_write_record(struct record_header *rh,
			struct mem_write_record *mwr)
{
	unsigned recorded_write_size;
	void *recorded_write;
	int safe;

#if MEMORY_DIRECTS_SEARCH
	run_client(get_thread(rh->tid), "forced by write record");
#else
	run_client(current_thread, "write record");
#endif

	if (mem_access_counter++ % SEARCH_SEES_EVERY_NTH_MEMORY_ACCESS == 0) {
		replay_assert_XXX(current_thread->id == rh->tid,
				  "wanted to be in thread %d, was in %d for write",
				  rh->tid,
				  current_thread->id);
		replay_assert_XXX(client_stop_reason.cls == CLIENT_STOP_mem_write,
				  "wanted a memory write, got class %d",
				  client_stop_reason.cls);
		replay_assert_XXX(client_stop_reason.u.mem_write.ptr == mwr->ptr,
				  "Expected a write to %p, got one to %p",
				  mwr->ptr,
				  client_stop_reason.u.mem_read.ptr);
		recorded_write_size = rh->size - sizeof(*rh) - sizeof(*mwr);
		recorded_write = mwr + 1;
		replay_assert_XXX(client_stop_reason.u.mem_write.size == recorded_write_size,
				  "wanted write of size %d, got size %d",
				  recorded_write_size, client_stop_reason.u.mem_write.size);

		if (mwr->ptr == MAGIC_PTR)
			VG_(printf)("Thread %d(%d) writes %x\n",
				    current_thread->id,
				    rh->tid,
				    *(unsigned *)client_stop_reason.u.mem_read.buffer);

		safe = 1;
		if (VG_(memcmp)(client_stop_reason.u.mem_write.buffer,
				recorded_write,
				recorded_write_size)) {
			safe = 0;
			switch (recorded_write_size) {
			case 4:
				if (*(unsigned *)client_stop_reason.u.mem_write.buffer == NONDETERMINISM_POISON)
					safe = 1;
				break;
			case 8:
				if (*(unsigned long *)client_stop_reason.u.mem_write.buffer == NONDETERMINISM_POISON)
					safe = 1;
				break;
			}
		}
		if (!safe)
			failure ("Memory divergence (write) at address %p; wanted %lx but got %lx (size %d)!\n",
				 mwr->ptr,
				 *(unsigned long *)recorded_write,
				 *(unsigned long *)mwr->ptr,
				 recorded_write_size);
	}
	finish_this_record(&logfile);
}

static void
block_thread(ThreadId id)
{
	struct replay_thread *rt = get_thread(id);
	rt->blocked = True;
	finish_this_record(&logfile);
	if (rt == current_thread)
		reschedule(True, "thread blocking");
	return;
}

static void
unblock_thread(ThreadId id)
{
	struct replay_thread *rt = get_thread(id);
	rt->blocked = False;
	finish_this_record(&logfile);
	reschedule(True, "thread unblocking");
	return;
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

static struct replay_thread *
spawning_thread;

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
	run_coroutine(&head_thread->coroutine, &replay_state_machine);
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

	VG_(running_tid) = VG_INVALID_THREADID;
	local_thread = current_thread;
	VG_(in_generated_code) = False;
	run_client(spawning_thread, "newly spawning thread");
	current_thread = local_thread;
	VG_(running_tid) = local_thread->id;
	VG_(in_generated_code) = True;

	rt->next_thread = head_thread;
	head_thread = rt;

	reschedule(True, "clone syscall");

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
