#include <asm/unistd.h>
#include <setjmp.h>
#include <stddef.h>

#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcsignal.h"
#include "pub_tool_signals.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "libvex_trc_values.h"
#include "valgrind.h"

#include "ppres.h"
#include "coroutines.h"
#include "replay.h"

extern Bool VG_(in_generated_code);
extern ThreadId VG_(running_tid);
extern Bool VG_(tool_handles_synchronisation);
extern ULong (*tool_provided_rdtsc)(void);

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
};

static struct client_event_record *
client_event;

static struct coroutine
replay_machine;

static struct replay_thread *
head_thread;

static struct replay_thread *
current_thread;

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

	cer->type = EVENT_nothing;
	current_thread = rt;
	client_event = cer;

	run_coroutine(&replay_machine,
		      &rt->coroutine,
		      "run_thread");

	tl_assert(cer == client_event);
	tl_assert(rt == current_thread);
	client_event = NULL;
	current_thread = NULL;

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
	event(EVENT_footstep, rip, rdx, rcx, rax);
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
	VG_(memcpy)(read_bytes, ptr, size);
	event(EVENT_load, (unsigned long)ptr, size,
	      (unsigned long)read_bytes);
}

static void
store_event(void *ptr, unsigned size, const void *written_bytes)
{
	event(EVENT_store, (unsigned long)ptr, size,
	      (unsigned long)written_bytes);
	VG_(memcpy)(ptr, written_bytes, size);
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

#define replay_assert_eq(a, b)                                             \
do {                                                                       \
	if ((a) != (b)) {                                                  \
		VG_(printf)("Replay failed at %d: %s(%lx) != %s(%lx)\n",   \
			    __LINE__,                                      \
                            #a,                                            \
			    (unsigned long)(a),				   \
			    #b,                                            \
			    (unsigned long)(b));			   \
		my__exit(1);                                               \
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
	case __NR_open:
	case __NR_read:
	case __NR_stat:
	case __NR_uname:
		state->guest_RAX = sysres_to_eax(sr->syscall_res);
		finish_this_record(logfile);
		break;

		/* Moderately easy syscalls: run them and assert that
		   the result is the same. */
	case __NR_arch_prctl:
	case __NR_brk:
	case __NR_mprotect:
	case __NR_munmap:
		VG_(client_syscall)(VG_(running_tid),
				    VEX_TRC_JMP_SYS_SYSCALL);
		tl_assert(sysres_to_eax(sr->syscall_res) == state->guest_RAX);
		finish_this_record(logfile);
		break;

	case __NR_exit_group:
		VG_(printf)("Exit group.\n");
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
		replay_syscall(sr, event, logfile);
		break;
	}
	default:
		finish_this_record(logfile);
		break;
	}
}

/* The replay machine itself.  This consumes records from the log file
   and decides how we're going to try to satisfy them. */
static void
replay_machine_fn(void)
{
	struct record_consumer logfile;
	const struct record_header *rec;
	struct replay_thread *thr;
	struct client_event_record thread_event;

	VG_(printf)("Replay machine starting.\n");

	open_logfile(&logfile, (Char *)"logfile1");

	while (1) {
		rec = get_current_record(&logfile);
		if (!rec)
			break;

		tl_assert(rec->cls != RECORD_memory);
		ASSUME(rec->cls != RECORD_client);

		thr = get_thread_by_id(rec->tid);
		tl_assert(thr != NULL);

		ASSUME(!thr->failed);

		run_thread(thr, &thread_event);

		ASSUME(thread_event.type != EVENT_resched_candidate);

		validate_event(rec, &thread_event);

		replay_record(rec, thr, &thread_event, &logfile); /* Finishes the record */
	}

	VG_(printf)("Hit end of log.\n");
	my__exit(0);
}

static void
init(void)
{
	head_thread = VG_(malloc)("head thread", sizeof(*head_thread));
	VG_(memset)(head_thread, 0, sizeof(*head_thread));
	head_thread->id = 1;
	initialise_coroutine(&head_thread->coroutine, "head thread");

	VG_(printf)("Running replay machine.\n");
	run_coroutine(&head_thread->coroutine, &replay_machine,
		      "start of day");
	VG_(printf)("Replay machine starts the world.\n");
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

	VG_(details_name)((signed char *)"ppres_rep");
	VG_(details_version)((signed char *)"0.0");
	VG_(details_copyright_author)((signed char *)"Steven Smith");
	VG_(details_bug_reports_to)((signed char *)"sos22@cam.ac.uk");
	VG_(details_description)((signed char *)"Replayer for PPRES");
	VG_(basic_tool_funcs)(init, instrument_func, fini);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
