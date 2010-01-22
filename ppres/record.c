#define _LARGEFILE64_SOURCE
#include <asm/unistd.h>
#include <sys/mman.h>
#include <sys/fcntl.h>
#include <sys/resource.h>
#include <linux/sched.h>
#include <linux/utsname.h>
#include <linux/futex.h>
#include <errno.h>
#include <setjmp.h>
#include <time.h>
#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_signals.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcsignal.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"
#include "valgrind.h"

#include "ppres.h"

extern ULong (*tool_provided_rdtsc)(void);

#define DEBUG(fmt, args...) //VG_(printf)(fmt, ## args)

#define RECORD_BLOCK_SIZE 16384
#define MAX_RECORD_SIZE 4096

struct record_emitter {
	int fd;
	void *current_block;
	unsigned current_block_used;
};

static struct record_emitter
logfile;

static void
open_logfile(struct record_emitter *res,
	     const signed char *fname)
{
	SysRes open_res;

	open_res = VG_(open)(fname, O_WRONLY|O_CREAT|O_TRUNC|O_LARGEFILE,
			     0700);
	res->fd = sr_Res(open_res);
	res->current_block = VG_(malloc)("logbuffer",
					 RECORD_BLOCK_SIZE);
	res->current_block_used = 0;
}

struct thread_info {
	struct thread_info *next;
	ThreadId id;
	Bool in_monitor;
};

static struct thread_info *
head_thread_info;

static struct thread_info *
get_thread_info(ThreadId id)
{
	struct thread_info *t;
	for (t = head_thread_info; t && t->id != id; t = t->next)
		;
	if (t)
		return t;
	t = VG_(malloc)("thread info", sizeof(*t));
	VG_(memset)(t, 0, sizeof(*t));
	t->next = head_thread_info;
	t->id = id;
	t->in_monitor = False;
	head_thread_info = t;
	return t;
}

static void
client_entering_monitor(ThreadId tid)
{
	get_thread_info(tid)->in_monitor = True;
}

static void
client_exiting_monitor(ThreadId tid)
{
	get_thread_info(tid)->in_monitor = False;
}

static Bool
client_in_monitor(void)
{
	return get_thread_info(VG_(get_running_tid)())->in_monitor;
}

static void *
emit_record(struct record_emitter *re,
	    unsigned record_class,
	    unsigned record_size)
{
	struct record_header *hdr;

	tl_assert(record_size <= MAX_RECORD_SIZE);
	record_size += sizeof(*hdr);
	if (re->current_block_used + record_size > RECORD_BLOCK_SIZE) {
		VG_(write)(re->fd, re->current_block,
			   re->current_block_used);
		re->current_block_used = 0;
	}
	hdr = re->current_block + re->current_block_used;
	hdr->cls = record_class;
	hdr->size = record_size;
	hdr->tid = VG_(get_running_tid)();
	re->current_block_used += record_size;
	return hdr + 1;
}

static void
close_logfile(struct record_emitter *re)
{
	if (re->current_block_used != 0)
		VG_(write)(re->fd, re->current_block, re->current_block_used);
	VG_(close)(re->fd);
	VG_(free)(re->current_block);
	re->current_block = NULL;
	re->fd = -1;
}



static void
record_instr(Word addr, Word rdx, Word rcx, Word rax)
{
	struct footstep_record *fr;
	if (client_in_monitor())
		return;
	fr = emit_record(&logfile, RECORD_footstep, sizeof(*fr));
	fr->rip = addr;
	fr->rdx = rdx;
	fr->rcx = rcx;
	fr->rax = rax;
}

static void
record_load(const void *ptr, unsigned size, void *base)
{
	struct mem_read_record *mrr;
	VG_(memcpy)(base, ptr, size);
	if (!client_in_monitor()) {
		mrr = emit_record(&logfile, RECORD_mem_read, sizeof(*mrr) + size);
		mrr->ptr = (void *)ptr;
		VG_(memcpy)(mrr + 1, base, size);
	}
}

static void
record_store(void *ptr, unsigned size, const void *base)
{
	struct mem_write_record *mrr;
	VG_(memcpy)(ptr, base, size);
	if (!client_in_monitor()) {
		mrr = emit_record(&logfile, RECORD_mem_write, sizeof(*mrr) + size);
		mrr->ptr = ptr;
		VG_(memcpy)(mrr + 1, base, size);
	}
}

#define included_for_record
#include "transform_expr.c"

struct kernel_stat {
        unsigned long   st_dev;
        unsigned long   st_ino;
        unsigned long   st_nlink;

        unsigned int    st_mode;
        unsigned int    st_uid;
        unsigned int    st_gid;
        unsigned int    __pad0;
        unsigned long   st_rdev;
        long            st_size;
        long            st_blksize;
        long            st_blocks;      /* Number 512-byte blocks allocated. */

        unsigned long   st_atime;
        unsigned long   st_atime_nsec;
        unsigned long   st_mtime;
        unsigned long   st_mtime_nsec;
        unsigned long   st_ctime;
        unsigned long   st_ctime_nsec;
        long            __unused[3];
};

static void
emit_triv_syscall(UInt nr, SysRes res, UWord *args)
{
	struct syscall_record *sr;

	tl_assert(!client_in_monitor());

	sr = emit_record(&logfile, RECORD_syscall, sizeof(*sr));
	sr->syscall_nr = nr;
	sr->syscall_res = res;
	sr->arg1 = args[0];
	sr->arg2 = args[1];
	sr->arg3 = args[2];
}

static jmp_buf
capture_memory_jmpbuf;

static void
capture_memory_sighandler(Int signo, Addr addr)
{
	if (signo == VKI_SIGBUS) {
		/* Whoops.  We tried to capture some memory which
		   didn't exist (e.g. mmap past the end of a file).
		   Abort the capture, and just ignore everything past
		   this point. */
		__builtin_longjmp(capture_memory_jmpbuf, 1);
	}
}

static void
capture_memory_small(void *base, unsigned size)
{
	struct memory_record *mr;

	mr = emit_record(&logfile, RECORD_memory, sizeof(*mr) + size);
	mr->ptr = base;
	VG_(memcpy)(mr + 1, base, size);
}

static void
capture_memory(void *base, unsigned size)
{
	unsigned this_time;
	vki_sigset_t sigmask;

	if (__builtin_setjmp(&capture_memory_jmpbuf)) {
		VG_(printf)("SIGBUS trying to capture memory.  Oh well.\n");
		VG_(set_fault_catcher)(NULL);
		VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
		return;
	}

	VG_(sigprocmask)(VKI_SIG_SETMASK, NULL, &sigmask);
	VG_(set_fault_catcher)(capture_memory_sighandler);

	while (size != 0) {
		this_time = size;
		if (this_time + sizeof(struct memory_record) >
		    MAX_RECORD_SIZE)
			this_time = MAX_RECORD_SIZE - sizeof(struct memory_record);
		capture_memory_small(base, this_time);
		size -= this_time;
		base += this_time;
	}

	VG_(set_fault_catcher)(NULL);
	VG_(sigprocmask)(VKI_SIG_SETMASK, &sigmask, NULL);
}

static void
pre_syscall(ThreadId tid, UInt syscall_nr, UWord *syscall_args, UInt nr_args)
{
	if (client_in_monitor())
		return;

	switch (syscall_nr) {
	case __NR_mmap: {
		UWord flags = syscall_args[3];
		if (flags & MAP_SHARED) {
			VG_(printf)("WARNING: privatising shared memory mapping\n");
			flags &= ~MAP_SHARED;
			flags |= MAP_PRIVATE;
		}
		syscall_args[3] = flags;
		break;
	}
	case __NR_clone: {
		UWord flags = syscall_args[0];
		tl_assert(flags ==
			  (CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
			   CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS |
			   CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID));
		emit_record(&logfile, RECORD_new_thread, 0);
		break;
	}
	case __NR_futex: {
		switch (syscall_args[1]) {
		case FUTEX_WAIT_PRIVATE: {
			int expected;
			int observed;
			expected = syscall_args[2];
			observed = *(int *)syscall_args[0];
			if (expected == observed)
				emit_record(&logfile, RECORD_thread_blocking, 0);
			break;
		}
		}
		break;
	}
	}
}

static void
my_mprotect(void *base, size_t len, int prot)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_mprotect), "rdi" (base),
	     "rsi" (len), "rdx" (prot));
}

static void
post_syscall(ThreadId tid, UInt syscall_nr, UWord *syscall_args, UInt nr_args,
	     SysRes res)
{
	if (client_in_monitor())
		return;

	emit_triv_syscall(syscall_nr, res, syscall_args);

	switch (syscall_nr) {
	case __NR_brk:
	case __NR_access:
	case __NR_open:
	case __NR_mprotect:
	case __NR_close:
	case __NR_arch_prctl:
	case __NR_munmap:
	case __NR_write:
	case __NR_exit_group:
	case __NR_set_tid_address:
	case __NR_set_robust_list:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:
	case __NR_lseek:
	case __NR_exit:
	case __NR_getuid:
		break;

	case __NR_nanosleep: {
		if (!sr_isError(res))
			break;
		if (sr_Err(res) != EINTR)
			break;
		if (syscall_args[1] == 0)
			break;
		capture_memory((void *)syscall_args[1],
			       sizeof(struct timespec));
		break;
	}

	case __NR_clone: {
		UWord flags = syscall_args[0];
		VG_(printf)("Record clone flags %lx\n", flags);

		if (sr_isError(res))
			break;
		if (flags & CLONE_CHILD_SETTID) {
			VG_(printf)("Child ptr %lx\n",
				    syscall_args[3]);
			capture_memory((void *)syscall_args[2], 4);
		}
		if (flags & CLONE_PARENT_SETTID) {
			VG_(printf)("Parent ptr %lx (%x)\n",
				    syscall_args[4],
				    *(unsigned *)(syscall_args[3]));
			capture_memory((void *)syscall_args[3], 4);
		}
		break;
	}

	case __NR_mmap: {
		UWord addr;
		UWord length = syscall_args[1];
		UWord prot = syscall_args[2];
		UWord new_prot;

		if (sr_isError(res))
			break;
		addr = sr_Res(res);
		new_prot = prot | PROT_READ;
		if (new_prot != prot)
			my_mprotect((void *)addr, length, new_prot);
		capture_memory((void *)addr, length);
		if (new_prot != prot)
			my_mprotect((void *)addr, length, prot);
		break;
	}

	case __NR_uname: {
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[0],
				       sizeof(struct new_utsname));
		break;
	}

	case __NR_read: {
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[1],
				       sr_Res(res));
		break;
	}

	case __NR_stat:
	case __NR_fstat: {
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[1],
				       sizeof(struct kernel_stat));
		break;
	}

	case __NR_getcwd: {
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[0],
				       sr_Res(res));
		break;
	}

	case __NR_getrlimit:
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[1],
				       sizeof(struct rlimit));
		break;

	case __NR_clock_gettime:
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[1],
				       sizeof(struct timespec));
		break;

	case __NR_futex: {
		switch (syscall_args[1]) {
		case FUTEX_WAKE_PRIVATE:
			/* No special handling needed */
			break;
		case FUTEX_WAIT_PRIVATE:
			if (!sr_isError(res) ||
			    sr_Err(res) != EWOULDBLOCK)
				emit_record(&logfile, RECORD_thread_unblocked, 0);
			break;
		default:
			VG_(printf)("Don't understand futex operation %ld\n",
				    syscall_args[1]);
			VG_(tool_panic)((Char *)"Not implemented yet");
		}
		break;
	}

	default:
		VG_(printf)("don't know what to do with syscall %d\n", syscall_nr);
		VG_(exit)(1);
	}
}

static void
init(void)
{
	open_logfile(&logfile, (signed char *)"logfile1");
}

static void
fini(Int ignore)
{
	close_logfile(&logfile);
}

static ULong
record_rdtsc(void)
{
	UInt eax, edx;
	ULong res;
	struct rdtsc_record *rr;

	__asm__ __volatile__("rdtsc" : "=a" (eax), "=d" (edx));
	res = (((ULong)edx) << 32) | ((ULong)eax);
	if (!client_in_monitor()) {
		rr = emit_record(&logfile, RECORD_rdtsc, sizeof(*rr));
		rr->stashed_tsc = res;
		VG_(printf)("Recorded a RDTSC.\n");
	}
	return res;
}

static Bool
handle_client_request(ThreadId tid, UWord *arg_block, UWord *ret)
{
	struct client_req_record *crr;

	if (VG_IS_TOOL_USERREQ('P', 'P', arg_block[0])) {
		crr = emit_record(&logfile, RECORD_client, sizeof(*crr));
		crr->flavour = arg_block[0];
		*ret = 0;
		return True;
	} else if (VG_IS_TOOL_USERREQ('E', 'A', arg_block[0])) {
		if ((arg_block[0] & 0xffff) == 0) {
			client_entering_monitor(tid);
		} else {
			client_exiting_monitor(tid);
		}
		*ret = 0;
		return True;
	} else {
		return False;
	}
}

static void
pre_clo_init(void)
{
	tool_provided_rdtsc = record_rdtsc;

	VG_(details_name)((signed char *)"ppres_rec");
	VG_(details_version)((signed char *)"0.0");
	VG_(details_copyright_author)((signed char *)"Steven Smith");
	VG_(details_bug_reports_to)((signed char *)"sos22@cam.ac.uk");
	VG_(details_description)((signed char *)"Simple flight data record for PPRES");
	VG_(basic_tool_funcs)(init, instrument_func, fini);
	VG_(needs_syscall_wrapper)(pre_syscall, post_syscall);
	VG_(needs_client_requests)(handle_client_request);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
