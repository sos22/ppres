#define _LARGEFILE64_SOURCE
#include <asm/unistd.h>
#include <sys/mman.h>
#include <sys/fcntl.h>
#include <sys/resource.h>
#include <linux/utsname.h>
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
#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"
#include "libvex_guest_amd64.h"

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



static Addr64
record_instr(VexGuestAMD64State *state, Word addr)
{
	struct footstep_record *fr;
	fr = emit_record(&logfile, RECORD_footstep, sizeof(*fr));
	fr->rip = addr;
	fr->rdx = state->guest_RDX;
	fr->rcx = state->guest_RCX;
	fr->rax = state->guest_RAX;
	return addr;
}

static IRSB *
instrument_func(VgCallbackClosure *closure,
		IRSB *sb_in,
		VexGuestLayout *layout,
		VexGuestExtents *vge,
		IRType gWordTy,
		IRType hWordTy)
{
	IRSB *sb_out;
	IRStmt *current_in_stmt;
	IRStmt *out_stmt;
	unsigned i;
	IRDirty *helper;

	sb_out = deepCopyIRSBExceptStmts(sb_in);
	for (i = 0; i < sb_in->stmts_used; i++) {
		current_in_stmt = sb_in->stmts[i];
		if (current_in_stmt->tag == Ist_IMark) {
			helper = unsafeIRDirty_0_N(
				1,
				"record_instr",
				VG_(fnptr_to_fnentry)(record_instr),
				mkIRExprVec_1(
					IRExpr_Const(IRConst_U64(current_in_stmt->Ist.IMark.addr))));

			helper->needsBBP = True;

			helper->mFx = Ifx_Modify;
			helper->mAddr = IRExpr_Const(IRConst_U64(0));
			helper->mSize = -1;

			helper->nFxState = 1;
			helper->fxState[0].fx = Ifx_Modify;
			helper->fxState[0].offset = 0;
			helper->fxState[0].size = sizeof(VexGuestAMD64State);

			out_stmt = IRStmt_Dirty(helper);
			addStmtToIRSB(sb_out, out_stmt);
		}
		out_stmt = deepCopyIRStmt(current_in_stmt);
		addStmtToIRSB(sb_out, out_stmt);
	}
	return sb_out;
}

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
emit_triv_syscall(UInt nr, SysRes res)
{
	struct syscall_record *sr;

	sr = emit_record(&logfile, RECORD_syscall, sizeof(*sr));
	sr->syscall_nr = nr;
	sr->syscall_res = res;
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
	emit_triv_syscall(syscall_nr, res);

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
	case __NR_futex:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:
	case __NR_lseek:
		break;

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
	rr = emit_record(&logfile, RECORD_rdtsc, sizeof(*rr));
	rr->stashed_tsc = res;
	VG_(printf)("Recorded a RDTSC.\n");
	return res;
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
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
