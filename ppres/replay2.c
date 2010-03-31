#include <asm/unistd.h>
#include <linux/futex.h>
#include <errno.h>
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

#include "../coregrind/pub_core_threadstate.h"

#include "ppres.h"
#include "ppres_client.h"
#include "replay.h"
#include "replay2.h"

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

static void run_to(struct record_consumer *logfile, replay_coord_t to, Bool stop_on_event);
static void next_record(void);

struct failure_reason {
	unsigned reason;
	unsigned tid;
	unsigned wanted_tid;
	const struct expression *arg1;
	const struct expression *arg2;
};

static Bool
use_memory;

struct client_event_record *
client_event;

static struct coroutine
replay_machine;

struct replay_thread *
current_thread;

static int
control_process_socket;

static Bool
trace_mode;

static Addr
trace_address;

struct replay_thread *
head_thread;

struct interpret_mem_lookaside *
head_interpret_mem_lookaside;

Bool
want_to_interpret;

struct record_consumer
logfile;

replay_coord_t
now;

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

int
my_sigaction(int sig, const struct vki_sigaction_base *new,
	     struct vki_sigaction_base *old)
{
	int res;
	register unsigned long sigset_size asm ("r10");
	sigset_size = sizeof(vki_sigset_t);
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_rt_sigaction),
	       "D" (sig),
	       "S" (new),
	       "d" (old),
	       "r" (sigset_size));
	return res;
}

void
my_sleep(unsigned x)
{
	struct {
		time_t tv_sec;
		long tv_nsec;
	}ts;
	unsigned res;

	ts.tv_sec = x;
	ts.tv_nsec = 0;
	while (1) {
		asm volatile ("syscall"
			      : "=a" (res)
			      : "0" (__NR_nanosleep),
				"D" (&ts),
				"S" (&ts));
		if (res == 0)
			return;
	}
}

/* Safe against partial writes, but kills you if it hits any other
   errors. */
void
safeish_write(int fd, const void *buffer, size_t buffer_size)
{
	unsigned x;
	Int this_time;

	for (x = 0; x < buffer_size; ) {
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

	for (x = 0; x < buffer_size; ) {
		this_time = VG_(read)(fd, buffer + x, buffer_size - x);
		if (this_time <= 0) {
			if (this_time == 0) {
				VG_(printf)("Control process hung up on us.\n");
				my__exit(1);
			}
			VG_(tool_panic)((Char *)"reading");
		}
		x += this_time;
	}
}

static jmp_buf
safe_memcpy_jmpbuf;

static void
safe_memcpy_sighandler(Int signo, Addr addr)
{
	if (signo == VKI_SIGBUS || signo == VKI_SIGSEGV)
		__builtin_longjmp(safe_memcpy_jmpbuf, 1);
}

Bool
safe_memcpy(void *dest, const void *src, unsigned size)
{
	vki_sigset_t sigmask;
	Bool should_be_in_gen;

	should_be_in_gen = VG_(in_generated_code);
	check_fpu_control();
	if (__builtin_setjmp(&safe_memcpy_jmpbuf)) {
		/* longjmp(), for some reason, clobbers the FPU
		   control work.  Put it back. */
		load_fpu_control();
		check_fpu_control();
		VG_(in_generated_code) = should_be_in_gen;
		VG_(set_fault_catcher)(NULL);
		VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
		return False;
	}
	VG_(in_generated_code) = False;
	VG_(sigprocmask)(VKI_SIG_SETMASK, NULL, &sigmask);
	VG_(set_fault_catcher)(safe_memcpy_sighandler);
	VG_(memcpy)(dest, src, size);
	VG_(set_fault_catcher)(NULL);
	VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
	VG_(in_generated_code) = should_be_in_gen;
	check_fpu_control();

	return True;
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

void
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

static void
send_string(const char *buf)
{
	struct response_message msg;
	struct response_string rs;
	msg.response = RESPONSE_STRING;
	rs.len = VG_(strlen)((Char *)buf);
	safeish_write(control_process_socket, &msg, sizeof(msg));
	safeish_write(control_process_socket, &rs, sizeof(rs));
	safeish_write(control_process_socket, buf, rs.len);
}

/* This can handle the case where buf isn't a valid pointer.  It
 * automatically sends either an OK or an error. */
static void
send_bytes(unsigned size, const void *buf)
{
	struct response_message msg;
	struct response_string rs;
	unsigned x;
	Int this_time;

	msg.response = RESPONSE_BYTES;
	rs.len = size;
	safeish_write(control_process_socket, &msg, sizeof(msg));
	safeish_write(control_process_socket, &rs, sizeof(rs));

	for (x = 0; x < size; ) {
		this_time = VG_(write)(control_process_socket,
				       buf + x, size - x);
		if (this_time <= 0) {
			/* Failed; probably a bad pointer.  Output
			 * zeroes to regain synchronisation, and then
			 * report an error. */
			unsigned char zero = 0;
			while (x < size) {
				/* Ignore errors */
				VG_(write)(control_process_socket, &zero, 1);
				x++;
			}
			send_error();
			return;
		}
		x += this_time;
	}
	send_okay();
}

static void
get_control_command(struct control_command *cmd)
{
	struct command_header ch;
	unsigned x;

	safeish_read(control_process_socket, &ch, sizeof(ch));
	cmd->cmd = ch.command;
	tl_assert(ch.nr_args < 4);
	for (x = 0; x < ch.nr_args; x++)
		safeish_read(control_process_socket, &cmd->u.args[x], 8);
	switch (ch.command) {
	case WORKER_SNAPSHOT:
	case WORKER_KILL:
	case WORKER_THREAD_STATE:
	case WORKER_REPLAY_STATE:
	case WORKER_GET_THREAD:
	case WORKER_GET_REGISTERS:
	case WORKER_GET_HISTORY:
	case WORKER_GET_LOG_PTR:
		tl_assert(ch.nr_args == 0);
		break;
	case WORKER_RUN:
	case WORKER_TRACE_TO_EVENT:
	case WORKER_TRACE:
	case WORKER_CONTROL_TRACE:
	case WORKER_VG_INTERMEDIATE:
	case WORKER_SET_THREAD:
	case WORKER_RUN_SYSCALL:
		tl_assert(ch.nr_args == 1);
		break;
	case WORKER_TRACE_ADDRESS:
	case WORKER_GET_MEMORY:
	case WORKER_SET_MEMORY:
	case WORKER_SET_TSC:
	case WORKER_SET_LOG_PTR:
		tl_assert(ch.nr_args == 2);
		break;
	case WORKER_SET_REGISTER:
	case WORKER_ALLOCATE_MEMORY:
	case WORKER_SET_MEMORY_PROTECTION:
		tl_assert(ch.nr_args == 3);
		break;
	}
	debug_control_command(cmd);
	return;
}

#define _TRACE(code, args...)                             \
	send_ancillary(ANCILLARY_TRACE_ ## code,	  \
		       now.access_nr,			  \
		       current_thread->id,		  \
		       ## args)

#define TRACE(code, args...)						\
	do {								\
		if (trace_mode) _TRACE(code, ## args);			\
		debug_trace_data(ANCILLARY_TRACE_ ## code, ## args);	\
	} while (0)

#define ALWAYS_TRACE(code, args...)					\
	do {								\
		_TRACE(code, ## args);					\
		debug_trace_data(ANCILLARY_TRACE_ ## code, ## args);	\
	} while (0)


/* Bits for managing the transitions between client code and the
   replay monitor. */

/* Run the client thread until it generates an event, and figure out
   what that event was. */
static void
run_thread(struct client_event_record *cer)
{
	tl_assert(!VG_(in_generated_code));
	tl_assert(client_event == NULL);
	tl_assert(VG_(running_tid) == VG_INVALID_THREADID);
	tl_assert(!current_thread->dead);

	current_thread->last_run = now;

	cer->type = EVENT_nothing;
	client_event = cer;
	VG_(running_tid) = current_thread->id;

	if (want_to_interpret) {
		VG_(interpret) = interpret_log_control_flow;
	} else {
		VG_(interpret) = NULL;
	}
	check_fpu_control();
	run_coroutine(&replay_machine,
		      &current_thread->coroutine,
		      "run_thread");
	check_fpu_control();

	tl_assert(cer == client_event);
	client_event = NULL;
	VG_(running_tid) = VG_INVALID_THREADID;

	tl_assert(cer->type != EVENT_nothing);
	tl_assert(!VG_(in_generated_code));
}

/* Something happened in the client which requires the monitor to do
   something. */
void
_client_event(void)
{
	tl_assert(VG_(in_generated_code));
	VG_(in_generated_code) = False;
	check_fpu_control();
	run_coroutine(&current_thread->coroutine,
		      &replay_machine,
		      "_client_event");
	check_fpu_control();
	tl_assert(VG_(running_tid) == current_thread->id);
	VG_(in_generated_code) = True;
}

/* The various events.  These are the bits which run in client
   context. */
void
footstep_event(Addr rip, Word rdx, Word rcx, Word rax, unsigned long xmm3a,
	       unsigned long xmm0a)
{
	check_fpu_control();
	if (!current_thread->in_monitor) {
		current_thread->last_rip = rip;
		TRACE(FOOTSTEP, rip, rdx, rcx, rax);
	}
	check_fpu_control();
}

void
syscall_event(VexGuestAMD64State *state)
{
	check_fpu_control();
	/* sys futex needs special handling so that we
	   generate block and unblock events in the right
	   places. */
	if (state->guest_RAX == __NR_futex) {
		unsigned long futex_cmd = state->guest_RSI & FUTEX_CMD_MASK;
		if (futex_cmd == FUTEX_WAIT ||
		    futex_cmd == FUTEX_WAIT_BITSET) {
			int observed;

			load_event((int *)state->guest_RDI, 4, &observed, 0, state->guest_RIP);
		}
	}
	TRACE(SYSCALL, state->guest_RAX);
	now.access_nr++;
	event(EVENT_syscall, state->guest_RAX, state->guest_RDI,
	      state->guest_RSI, state->guest_RDX, (unsigned long)state);
	check_fpu_control();
}

static ULong
rdtsc_event(void)
{
	check_fpu_control();
	if (current_thread->in_monitor) {
		/* This is obviously non-deterministic.  We rely on
		   the in-client monitor code to do the right
		   thing. */
		unsigned eax, edx;
		__asm__ __volatile__("rdtsc" : "=a" (eax), "=d" (edx));
		check_fpu_control();
		return (((ULong)edx) << 32) | ((ULong)eax);
	} else {
		TRACE(RDTSC);
		VG_(printf)("rdtsc event in access number %ld\n", now.access_nr);
		now.access_nr++;
		event(EVENT_rdtsc);
		check_fpu_control();
		return current_thread->rdtsc_result;
	}
}

static void
signal_event(ThreadId tid, Int signal, Bool alt_stack,
	     UWord err, UWord virtaddr, UWord rip)
{
	Bool in_gen = VG_(in_generated_code);

	load_fpu_control(); /* Signal delivery has a habit of screwing
			     * with FPU control flags.  Put them
			     * back. */

	/* XXX This isn't, strictly speaking, valid (the signal might
	   be caught and recovered from), but it's a reasonable
	   approximation for the time being. */
	current_thread->crashed = True;

	VG_(in_generated_code) = True;
	TRACE(SIGNAL, rip, signal, err, virtaddr);
	event(EVENT_signal, rip, signal, err, virtaddr);
	VG_(in_generated_code) = in_gen;
}

void
load_event(const void *ptr, unsigned size, void *read_bytes,
	   unsigned long rsp, unsigned long rip)
{
	while (!safe_memcpy(read_bytes, ptr, size)) {
		event(EVENT_signal, rip, 11, 4, (UWord)ptr);
	}
	check_fpu_control();
	if (IS_STACK(ptr, rsp)) {
		debug_trace_data(ANCILLARY_TRACE_LOAD,
				 size == 8 ?
				 *(unsigned long *)read_bytes :
				 *(unsigned long *)read_bytes & ((1ul << (size * 8)) - 1),
				 size,
				 (unsigned long)ptr,
				 current_thread->in_monitor);
		check_fpu_control();
		return;
	}
	if ( (ptr <= (const void *)trace_address &&
	      ptr + size > (const void *)trace_address) ||
	     (trace_mode)) {
		ALWAYS_TRACE(LOAD,
		       size == 8 ?
		       *(unsigned long *)read_bytes :
		       *(unsigned long *)read_bytes & ((1ul << (size * 8)) - 1),
		       size,
		       (unsigned long)ptr,
		       current_thread->in_monitor,
		       rip);
	}
	now.access_nr++;
	event(EVENT_load, (unsigned long)ptr, size,
	      (unsigned long)read_bytes);
	check_fpu_control();
}

void
store_event(void *ptr, unsigned size, const void *written_bytes,
	    unsigned long rsp, unsigned long rip)
{
	check_fpu_control();
	while (!safe_memcpy(ptr, written_bytes, size)) {
		event(EVENT_signal, rip, 11, 4, (UWord)ptr);
	}
	check_fpu_control();
	if (IS_STACK(ptr, rsp)) {
		debug_trace_data(ANCILLARY_TRACE_STORE,
				 size == 8 ?
				 *(unsigned long *)written_bytes :
				 *(unsigned long *)written_bytes & ((1ul << (size * 8)) - 1),
				 size,
				 (unsigned long)ptr,
				 current_thread->in_monitor);
		check_fpu_control();
		return;
	}
	if ( (ptr <= (const void *)trace_address &&
	      ptr + size > (const void *)trace_address) ||
	     (trace_mode)) {
		ALWAYS_TRACE(STORE,
		       size == 8 ?
		       *(unsigned long *)written_bytes :
		       *(unsigned long *)written_bytes & ((1ul << (size * 8)) - 1),
		       size,
		       (unsigned long)ptr,
		       current_thread->in_monitor,
		       rip);
	}
	now.access_nr++;
	event(EVENT_store, (unsigned long)ptr, size,
	      (unsigned long)written_bytes);
	check_fpu_control();
}

Bool
client_request_event(ThreadId tid, UWord *arg_block, UWord *ret)
{
	check_fpu_control();
	if (VG_IS_TOOL_USERREQ('P', 'P', arg_block[0])) {
		/* We are in generated code here, despite what
		   Valgrind might think about it. */
		VG_(in_generated_code) = True;
		if (trace_mode) {
			if (arg_block[0] == VG_USERREQ_PPRES_CALL_LIBRARY)
				ALWAYS_TRACE(CALLING);
			else
				ALWAYS_TRACE(CALLED);
			send_string((const char *)arg_block[1]);
		}
		now.access_nr++;
		event(EVENT_client_request, arg_block[0], arg_block[1]);
		VG_(in_generated_code) = False;
	} else if (VG_IS_TOOL_USERREQ('E', 'A', arg_block[0])) {
		if ((arg_block[0] & 0xffff) == 0) {
			TRACE(ENTER_MONITOR);
			current_thread->in_monitor = True;
		} else {
			TRACE(EXIT_MONITOR);
			current_thread->in_monitor = False;
		}
	}
	check_fpu_control();
	return False;
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
do_thread_state_command(void)
{
	struct replay_thread *rt;
	for (rt = head_thread; rt; rt = rt->next)
		send_ancillary(ANCILLARY_THREAD_STATE, rt->id, rt->dead, rt->crashed,
			       rt->last_run.access_nr, rt->last_rip);
	send_okay();
}

static void
do_get_registers_command(void)
{
	unsigned x;
	ThreadState *ts;
	unsigned long val;

	ts = VG_(get_ThreadState)(current_thread->id);
	for (x = 0; x <= REG_LAST; x++) {
		if (x >= REG_XMM0 && x <= REG_XMM_LAST) {
			/* Driver doesn't know about XMM
			 * registers; skip them. */
			continue;
		}
		if (want_to_interpret) {
			val = current_thread->interpret_state.registers[x].v;
		} else {
			val = (&ts->arch.vex.guest_RAX)[x];
		}
		send_ancillary(ANCILLARY_REG_BINDING, x, val);
	}
	send_okay();
}

static void
do_vg_intermediate_command(unsigned long addr)
{
	disassemble_addr(addr);
	send_okay();
}

struct history_entry {
	struct history_entry *next;
	unsigned nr_params;
	unsigned long params[];
};

static struct history_entry *
first_history_entry, *
last_history_entry;

static void
do_get_history_command(void)
{
	const struct history_entry *he;
	for (he = first_history_entry; he; he = he->next) {
		_send_ancillary(ANCILLARY_HISTORY_ENTRY,
				he->nr_params + 1,
				he->params);
	}
	send_okay();
}

static void
_history_append(unsigned key, const unsigned long *params,
		unsigned nr_params)
{
	struct history_entry *he;
	if (last_history_entry &&
	    last_history_entry->params[0] == key) {
		if (key == WORKER_RUN) {
			if (params[0] == last_history_entry->params[1]) {
				/* Run the same thread -> merge into previous
				 * entry */
				last_history_entry->params[2] = params[1];
				return;
			}
			if (params[1] == last_history_entry->params[2]) {
				/* Running for zero operations -> drop */
				return;
			}
		}
		if (key == WORKER_SET_LOG_PTR &&
		    params[0] == last_history_entry->params[1] &&
		    params[1] == last_history_entry->params[2]) {
			/* Set to where we already were -> drop */
			return;
		}
	}
	he = VG_(malloc)("history_entry",
			 sizeof(*he) + (nr_params+1) * sizeof(unsigned long));
	he->next = NULL;
	he->nr_params = nr_params;
	he->params[0] = key;
	VG_(memcpy)(he->params+1, params, nr_params * sizeof(params[0]));
	if (last_history_entry)
		last_history_entry->next = he;
	else
		first_history_entry = he;
	last_history_entry = he;
}

#define history_append(key, ...)				\
do {							        \
	unsigned long params[] = {__VA_ARGS__};			\
	_history_append(key, params,				\
			sizeof(params)/sizeof(params[0]));	\
} while (0)

#if 0
/* This is the bit of syscall replay which we haven't replicated into
   the driver yet. */
static void
replay_syscall(const struct syscall_record *sr,
	       struct client_event_record *event,
	       struct record_consumer *logfile)
{
	VexGuestAMD64State *state = (VexGuestAMD64State *)event->args[4];
	ThreadId tid;

	/* Keep valgrind happy */
	tid = VG_(running_tid);
	VG_(running_tid) = current_thread->id;

	switch (event->args[0]) {
	case __NR_exit:
		current_thread->dead = True;
		finish_this_record(logfile);
		break;

	case __NR_set_tid_address:
		if (!sr_isError(sr->syscall_res))
			VG_(client_syscall)(current_thread->id, VEX_TRC_JMP_SYS_SYSCALL);
		state->guest_RAX = sysres_to_eax(sr->syscall_res);;
		finish_this_record(logfile);
		break;

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
			VG_(printf)("Replaying clone syscall in %d:%ld\n",
				    logfile->record_nr, now.access_nr);
			VG_(running_tid) = tid;
			VG_(client_syscall)(current_thread->id, VEX_TRC_JMP_SYS_SYSCALL);
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

	VG_(running_tid) = tid;
}
#endif

static void
next_record(void)
{
	const struct record_header *rec;

	rec = get_current_record(&logfile);
	if (!rec)
		return;
	while (rec->cls == RECORD_new_thread ||
	       rec->cls == RECORD_thread_blocking ||
	       rec->cls == RECORD_thread_unblocked ||
	       rec->cls == RECORD_footstep ||
	       (!use_memory &&
		(rec->cls == RECORD_mem_read ||
		 rec->cls == RECORD_mem_write))) {
		finish_this_record(&logfile);
		rec = get_current_record(&logfile);
	}

//	current_thread = get_thread_by_id(rec->tid);
	tl_assert(current_thread != NULL);
}

static Bool
replay_coord_lt(replay_coord_t l, replay_coord_t r)
{
	if (l.access_nr < r.access_nr)
		return True;
	return False;
}

static void
run_to(struct record_consumer *logfile, replay_coord_t when, Bool stop_on_event)
{
	struct client_event_record thread_event;

	while (replay_coord_lt(now, when)) {
		while (1) {
			run_thread(&thread_event);
			if ((thread_event.type != EVENT_load &&
			     thread_event.type != EVENT_store) ||
			    use_memory)
				break;
			if (!replay_coord_lt(now, when)) {
				current_thread->last_run = now;
				history_append(WORKER_RUN, current_thread->id,
					       now.access_nr);
				return;
			}
		}

		current_thread->last_run = now;

		next_record();

		if (stop_on_event)
			break;
	}
	history_append(WORKER_RUN, current_thread->id, now.access_nr);
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
		run_to(logfile, cmd->u.run.when, False);
		send_okay();
		return;
	case WORKER_TRACE_TO_EVENT:
		trace_mode = True;
		run_to(logfile, cmd->u.run.when, True);
		trace_mode = False;
		send_okay();
		return;
	case WORKER_TRACE:
		trace_mode = True;
		run_to(logfile, cmd->u.trace.when, False);
		trace_mode = False;
		send_okay();
		return;
	case WORKER_CONTROL_TRACE:
		want_to_interpret = True;
		run_to(logfile, cmd->u.control_trace.when, False);
		want_to_interpret = False;
		send_okay();
		return;
	case WORKER_SNAPSHOT:
		control_process_socket = do_snapshot(control_process_socket);
		return;
	case WORKER_TRACE_ADDRESS:
		trace_address = cmd->u.trace_mem.address;
		run_to(logfile, cmd->u.trace_mem.when, False);
		send_okay();
		return;
	case WORKER_THREAD_STATE:
		do_thread_state_command();
		return;
	case WORKER_REPLAY_STATE:
		if (logfile->finished)
			send_ancillary(ANCILLARY_REPLAY_FINISHED, now.access_nr);
		else
			send_ancillary(ANCILLARY_REPLAY_SUCCESS, now.access_nr);
		send_okay();
		return;
	case WORKER_GET_MEMORY:
		send_bytes(cmd->u.get_memory.size, (const void *)cmd->u.get_memory.addr);
		return;
	case WORKER_VG_INTERMEDIATE:
		do_vg_intermediate_command(cmd->u.vg_intermediate.addr);
		return;
	case WORKER_GET_THREAD:
		send_ancillary(ANCILLARY_NEXT_THREAD, current_thread->id);
		send_okay();
		return;
	case WORKER_SET_THREAD:
		rt = get_thread_by_id(cmd->u.set_thread.tid);
		if (!rt) {
			VG_(printf)("Cannot find thread %ld\n", cmd->u.set_thread.tid);
			send_error();
		} else {
			current_thread = rt;
			send_okay();
		}
		return;
	case WORKER_GET_REGISTERS:
		do_get_registers_command();
		return;
	case WORKER_SET_REGISTER:
		if (cmd->u.set_register.reg > REG_LAST) {
			VG_(printf)("Register %ld unknown\n", cmd->u.set_register.reg);
			send_error();
			return;
		}

		rt = get_thread_by_id(cmd->u.set_register.tid);
		if (!rt) {
			VG_(printf)("bad thread %ld\n", cmd->u.set_register.tid);
			send_error();
			return;
		}

		history_append(WORKER_SET_REGISTER, rt->id, cmd->u.set_register.reg,
			       cmd->u.set_register.val);
		if (rt->interpret_state.live) {
			rt->interpret_state.registers[cmd->u.set_register.reg].v =
				cmd->u.set_register.val;
			rt->interpret_state.registers[cmd->u.set_register.reg].origin =
				expr_imported(cmd->u.set_register.val);
		} else {
			ThreadState *ts;
			ts = VG_(get_ThreadState)(cmd->u.set_register.tid);
			(&ts->arch.vex.guest_RAX)[cmd->u.set_register.reg] =
				cmd->u.set_register.val;
		}
		send_okay();
		return;
	case WORKER_ALLOCATE_MEMORY: {
		SysRes res;
		res = VG_(am_mmap_anon_fixed_client)(cmd->u.allocate_memory.addr,
						     cmd->u.allocate_memory.size,
						     cmd->u.allocate_memory.prot);
		if (sr_isError(res)) {
			send_error();
		} else {
			history_append(WORKER_ALLOCATE_MEMORY,
				       cmd->u.allocate_memory.addr,
				       cmd->u.allocate_memory.size,
				       cmd->u.allocate_memory.prot);
			send_okay();
		}
		return;
	}
	case WORKER_SET_MEMORY: {
		char buf[128];
		unsigned recved_this_time;
		unsigned recved_total;
		Bool worked;

		worked = True;
		for (recved_total = 0;
		     recved_total < cmd->u.set_memory.size;
		     recved_total += recved_this_time) {
			recved_this_time = cmd->u.set_memory.size - recved_total;
			if (recved_this_time > 128)
				recved_this_time = 128;
			safeish_read(control_process_socket,
				     buf,
				     recved_this_time);
			worked &= safe_memcpy((void *)(cmd->u.set_memory.addr + recved_total),
					      buf,
					      recved_this_time);
		}
		if (worked) {
			history_append(WORKER_SET_MEMORY,
				       cmd->u.set_memory.addr,
				       cmd->u.set_memory.size);
			send_okay();
		} else {
			send_error();
		}
		return;
	}
	case WORKER_SET_MEMORY_PROTECTION:
		history_append(WORKER_SET_MEMORY_PROTECTION,
			       cmd->u.set_memory_protection.addr,
			       cmd->u.set_memory_protection.size,
			       cmd->u.set_memory_protection.prot);
		my_mprotect((void *)cmd->u.set_memory_protection.addr,
			    cmd->u.set_memory_protection.size,
			    cmd->u.set_memory_protection.prot);
		send_okay();
		return;
	case WORKER_SET_TSC:
		rt = get_thread_by_id(cmd->u.set_tsc.tid);
		if (!rt) {
			VG_(printf)("set tsc in bad thread %ld\n",
				    cmd->u.set_tsc.tid);
			send_error();
		} else {
			rt->rdtsc_result = cmd->u.set_tsc.tsc;
			history_append(WORKER_SET_TSC,
				       cmd->u.set_tsc.tid,
				       cmd->u.set_tsc.tsc);
			send_okay();
		}
		return;
	case WORKER_GET_HISTORY:
		do_get_history_command();
		return;
	case WORKER_GET_LOG_PTR:
		send_ancillary(ANCILLARY_LOG_PTR, logfile_tell(logfile), logfile->record_nr);
		send_okay();
		return;
	case WORKER_SET_LOG_PTR:
		logfile_seek(logfile, cmd->u.set_log_ptr.ptr, cmd->u.set_log_ptr.record);
		history_append(WORKER_SET_LOG_PTR, cmd->u.set_log_ptr.ptr,
			       cmd->u.set_log_ptr.record);
		next_record();
		send_okay();
		return;
	case WORKER_RUN_SYSCALL:
		rt = get_thread_by_id(cmd->u.run_syscall.tid);
		if (!rt) {
			VG_(printf)("Cannot find thread %ld\n", cmd->u.run_syscall.tid);
			send_error();
		} else {
			ThreadId tid;
			history_append(WORKER_RUN_SYSCALL, cmd->u.run_syscall.tid);
			tid = VG_(running_tid);
			VG_(running_tid) = rt->id;
			if (rt->interpret_state.live) {
				commit_is_to_vex_state(&rt->interpret_state,
						       &VG_(get_ThreadState)(rt->id)->arch.vex);
				VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);
				initialise_is_for_vex_state(&rt->interpret_state,
							    &VG_(get_ThreadState)(rt->id)->arch.vex);
			} else {
				VG_(client_syscall)(rt->id, VEX_TRC_JMP_SYS_SYSCALL);
			}
			VG_(running_tid) = tid;
			send_okay();
		}
		return;
	}
	VG_(printf)("Worker command %x\n", cmd->cmd);
	VG_(tool_panic)((Char *)"Bad worker command");
}

/* The replay machine itself.  This consumes records from the log file
   and decides how we're going to try to satisfy them. */
static void
replay_machine_fn(void)
{
	struct control_command cmd;

	open_logfile(&logfile, (Char *)"logfile1");

	/* Prime the machine */
	next_record();

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

	current_thread = head_thread = VG_(malloc)("head thread", sizeof(*head_thread));
	VG_(memset)(head_thread, 0, sizeof(*head_thread));
	head_thread->id = 1;
	initialise_coroutine(&head_thread->coroutine, "head thread");

	check_fpu_control();
	run_coroutine(&head_thread->coroutine, &replay_machine,
		      "start of day");
	check_fpu_control();

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

	check_fpu_control();
	run_coroutine(&newly_spawning_thread->coroutine,
		      &creating_thread_coroutine,
		      "new_thread_starting");
	check_fpu_control();
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
	check_fpu_control();
	run_coroutine(&creating_thread_coroutine,
		      &newly_spawning_thread->coroutine,
		      "create new thread");
	check_fpu_control();

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

	load_fpu_control();

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
	VG_(track_pre_deliver_signal)(signal_event);
	VG_(needs_command_line_options)(process_cmd_line,
					print_usage,
					print_debug);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
