#define _LARGEFILE64_SOURCE
#include <asm/unistd.h>
#include <sys/mman.h>
#include <sys/fcntl.h>
#include <linux/utsname.h>
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
#include "pub_tool_threadstate.h"

#include "libvex_guest_amd64.h"
#include "libvex_trc_values.h"

#include "ppres.h"

extern ULong (*tool_provided_rdtsc)(void);

/* Shouldn't really be calling these from here.  Oh well. */
extern void VG_(client_syscall) ( ThreadId tid, UInt trc );
extern SysRes VG_(am_mmap_anon_fixed_client)( Addr start, SizeT length, UInt prot );

struct record_consumer {
	int fd;
	unsigned offset_in_current_chunk;
	unsigned avail_in_current_chunk;
	void *current_chunk;
};

static void
open_logfile(struct record_consumer *res,
	     const signed char *fname)
{
	SysRes open_res;

	open_res = VG_(open)(fname, O_RDONLY, 0);
	res->fd = sr_Res(open_res);
	res->current_chunk = VG_(malloc)("logbuffer",
					 RECORD_BLOCK_SIZE);
	res->offset_in_current_chunk = 0;
	res->avail_in_current_chunk = 0;
}

static void
close_logfile(struct record_consumer *rc)
{
	VG_(close)(rc->fd);
	VG_(free)(rc->current_chunk);
}

static void
advance_chunk(struct record_consumer *rc)
{
	unsigned to_read;
	Int actually_read;

	VG_(memmove)(rc->current_chunk,
		     rc->current_chunk + rc->offset_in_current_chunk,
		     rc->avail_in_current_chunk - rc->offset_in_current_chunk);
	rc->avail_in_current_chunk -= rc->offset_in_current_chunk;
	rc->offset_in_current_chunk = 0;
	to_read = RECORD_BLOCK_SIZE - rc->avail_in_current_chunk;
	actually_read =
		VG_(read)(rc->fd,
			  rc->current_chunk + rc->avail_in_current_chunk,
			  to_read);
	rc->avail_in_current_chunk += actually_read;
}

static struct record_header *
get_current_record(struct record_consumer *rc)
{
	struct record_header *res;

	if (rc->offset_in_current_chunk + sizeof(struct record_header) >
	    rc->avail_in_current_chunk)
		advance_chunk(rc);
	res = rc->current_chunk + rc->offset_in_current_chunk;
	if (rc->offset_in_current_chunk + res->size >
	    rc->avail_in_current_chunk) {
		advance_chunk(rc);
		res = rc->current_chunk + rc->offset_in_current_chunk;
	}
	return res;
}

static void
finish_this_record(struct record_consumer *rc)
{
	rc->offset_in_current_chunk += get_current_record(rc)->size;
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

static void
replay_memory(struct record_header *rh, struct memory_record *mr)
{
	VG_(memcpy)(mr->ptr, mr + 1, rh->size - sizeof(*mr) - sizeof(*rh));
}

static int
replay_syscall(VexGuestAMD64State *state)
{
	struct record_header *rh;
	struct syscall_record *sr;

	rh = get_current_record(&logfile);
	sr = (struct syscall_record *)(rh + 1);

	tl_assert(sr->syscall_nr == state->guest_RAX);

	switch (state->guest_RAX) {
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

		if (sr_isError(sr->syscall_res))
			state->guest_RAX = -sr_Err(sr->syscall_res);
		else
			state->guest_RAX = sr_Res(sr->syscall_res);
		finish_this_record(&logfile);
		return 1;

		/* Moderately easy syscalls: run them and assert that
		   the result is the same. */
	case __NR_brk:
	case __NR_mprotect:
	case __NR_arch_prctl:
	case __NR_munmap:
	case __NR_exit_group:
	case __NR_set_robust_list:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:

	case __NR_futex: /* XXX not quite right, but good enough for
			  * now. */

		VG_(client_syscall)(VG_(get_running_tid)(),
				    VEX_TRC_JMP_SYS_SYSCALL);
		if (sr_isError(sr->syscall_res))
			tl_assert(-state->guest_RAX ==
				  sr_Err(sr->syscall_res));
		else
			tl_assert(state->guest_RAX ==
				  sr_Res(sr->syscall_res));
		finish_this_record(&logfile);
		return 1;

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
		return 1;

	case __NR_mmap: {
		Addr addr;
		ULong length;
		SysRes map_res;
		Word prot;

		if (sr_isError(sr->syscall_res)) {
			state->guest_RAX = -sr_Err(sr->syscall_res);
			finish_this_record(&logfile);
			return 1;
		}
		addr = sr_Res(sr->syscall_res);
		length = state->guest_RSI;
		prot = state->guest_RDX;
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
		rh = get_current_record(&logfile);
		while (rh->cls == RECORD_memory) {
			replay_memory(rh, (struct memory_record *)(rh + 1));
			finish_this_record(&logfile);
			rh = get_current_record(&logfile);
		}
		if (!(prot & PROT_WRITE))
			my_mprotect((void *)addr, length, prot);
		state->guest_RAX = addr;
		return 1;
	}
	default:
		VG_(printf)("don't know how to replay syscall %lld yet\n",
			    state->guest_RAX);
		VG_(exit)(1);
	}
	return 0;
}

static void
replay_footstep(VexGuestAMD64State *state, Word rip,
		struct footstep_record *fr)
{
	tl_assert(rip == fr->rip);
	tl_assert(state->guest_RAX == fr->rax);
	tl_assert(state->guest_RDX == fr->rdx);
	if (state->guest_RCX != fr->rcx)
		VG_(printf)("Divergence on RCX.\n");
}

static int
replay_instr(VexGuestAMD64State *state, Word rip)
{
	struct record_header *rh;

	while (1) {
		rh = get_current_record(&logfile);
		switch (rh->cls) {
		case RECORD_footstep:
			replay_footstep(state, rip,
					(struct footstep_record *)(rh + 1));
			finish_this_record(&logfile);
			rh = get_current_record(&logfile);
			if (rh->cls == RECORD_footstep)
				return 0;
			break;
		case RECORD_syscall:
			return replay_syscall(state);
		case RECORD_memory:
			replay_memory(rh, (struct memory_record *)(rh + 1));
			finish_this_record(&logfile);
			break;
		case RECORD_rdtsc:
			/* Let the instruction run so as we can pick
			   the result up. */
			return 0;
		}
	}
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
	IRTemp helper_did_instruction;

	sb_out = deepCopyIRSBExceptStmts(sb_in);
	for (i = 0; i < sb_in->stmts_used; i++) {
		current_in_stmt = sb_in->stmts[i];
		if (current_in_stmt->tag == Ist_IMark) {
			helper_did_instruction =
				newIRTemp(sb_out->tyenv,
					  Ity_I8);
			helper = unsafeIRDirty_1_N(
				helper_did_instruction,
				1,
				"replay_instr",
				VG_(fnptr_to_fnentry)(replay_instr),
				mkIRExprVec_1(
					IRExpr_Const(IRConst_U64(current_in_stmt->Ist.IMark.addr))));

			/* For now, we ask Valgrind to give us the
			   entire world state, and to allow us to
			   modify it. */
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

			out_stmt = IRStmt_Exit(
				IRExpr_Binop(Iop_CmpNE8,
					     IRExpr_Const(IRConst_U8(0)),
					     IRExpr_RdTmp(helper_did_instruction)),
				Ijk_Boring,
				IRConst_U64(
					current_in_stmt->Ist.IMark.addr +
					current_in_stmt->Ist.IMark.len));
			addStmtToIRSB(sb_out, out_stmt);
		}
		out_stmt = deepCopyIRStmt(current_in_stmt);
		addStmtToIRSB(sb_out, out_stmt);
	}
	return sb_out;
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
replay_rdtsc(void)
{
	struct record_header *rh;
	struct rdtsc_record *rr;

	rh = get_current_record(&logfile);
	tl_assert(rh->cls == RECORD_rdtsc);
	rr = (struct rdtsc_record *)(rh + 1);
	VG_(printf)("Replay a rdtsc.\n");
	finish_this_record(&logfile);
	return rr->stashed_tsc;
}

static void
pre_clo_init(void)
{
	tool_provided_rdtsc = replay_rdtsc;

	VG_(details_name)((signed char *)"ppres_rep");
	VG_(details_version)((signed char *)"0.0");
	VG_(details_copyright_author)((signed char *)"Steven Smith");
	VG_(details_bug_reports_to)((signed char *)"sos22@cam.ac.uk");
	VG_(details_description)((signed char *)"Replayer for PPRES");
	VG_(basic_tool_funcs)(init, instrument_func, fini);
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
