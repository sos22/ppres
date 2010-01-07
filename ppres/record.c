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

static void
record_load(void *ptr, unsigned size, const void *base)
{
	struct mem_read_record *mrr;
	mrr = emit_record(&logfile, RECORD_mem_read, sizeof(*mrr) + size);
	mrr->ptr = ptr;
	VG_(memcpy)(mrr + 1, base, size);
}

static void
record_store(void *ptr, unsigned size, const void *base)
{
	struct mem_write_record *mrr;
	mrr = emit_record(&logfile, RECORD_mem_write, sizeof(*mrr) + size);
	mrr->ptr = ptr;
	VG_(memcpy)(mrr + 1, base, size);
}

#define mk_helper_load(typ, suffix)                    \
static typ                                             \
helper_load_ ## suffix (void *ptr, typ val)            \
{                                                      \
	record_load(ptr, sizeof(val), &val);           \
	return val;                                    \
}

#define mk_helper_store(typ, suffix)                   \
static void                                            \
helper_store_ ## suffix (void *ptr, typ val)           \
{                                                      \
	record_store(ptr, sizeof(val), &val);          \
}

#define mk_helpers(typ, suffix)                        \
mk_helper_load(typ, suffix)                            \
mk_helper_store(typ, suffix)

mk_helpers(unsigned char, 8)
mk_helpers(unsigned short, 16)
mk_helpers(unsigned, 32)
mk_helpers(unsigned long, 64)

typedef struct {
	unsigned long long a;
	unsigned long long b;
} ultralong_t;

mk_helpers(ultralong_t, 128)

static IRExpr *
log_reads_expr(IRExpr *exp)
{
	switch (exp->tag) {
	case Iex_Get:
	case Iex_Binder:
	case Iex_RdTmp:
		return exp;
	case Iex_GetI:
		return IRExpr_GetI(exp->Iex.GetI.descr,
				  log_reads_expr(exp->Iex.GetI.ix),
				  exp->Iex.GetI.bias);
	case Iex_Qop:
		return IRExpr_Qop(exp->Iex.Qop.op,
				 log_reads_expr(exp->Iex.Qop.arg1),
				 log_reads_expr(exp->Iex.Qop.arg2),
				 log_reads_expr(exp->Iex.Qop.arg3),
				 log_reads_expr(exp->Iex.Qop.arg4));
	case Iex_Triop:
		return IRExpr_Triop(exp->Iex.Triop.op,
				   log_reads_expr(exp->Iex.Triop.arg1),
				   log_reads_expr(exp->Iex.Triop.arg2),
				   log_reads_expr(exp->Iex.Triop.arg3));
	case Iex_Binop:
		return IRExpr_Binop(exp->Iex.Binop.op,
				   log_reads_expr(exp->Iex.Binop.arg1),
				   log_reads_expr(exp->Iex.Binop.arg2));
	case Iex_Unop:
		return IRExpr_Unop(exp->Iex.Unop.op,
				   log_reads_expr(exp->Iex.Unop.arg));
	case Iex_Load: {
		IRExpr **args;
		IRCallee *helper;
		IRExpr *cast_exp;
		args = NULL;
		switch (exp->Iex.Load.ty) {
		case Ity_INVALID:
			VG_(tool_panic)((signed char *)"Bad type 1");;
		case Ity_I1:
			VG_(tool_panic)((signed char *)"Bad type 2");
		case Ity_I8:
			helper = mkIRCallee(0, "helper_load_8",
					    VG_(fnptr_to_fnentry)(helper_load_8));
			cast_exp = IRExpr_Unop(Iop_8Uto64, exp);
			break;
		case Ity_I16:
			helper = mkIRCallee(0, "helper_load_16",
					    VG_(fnptr_to_fnentry)(helper_load_16));
			cast_exp = IRExpr_Unop(Iop_16Uto64, exp);
			break;
		case Ity_I32:
		case Ity_F32:
			helper = mkIRCallee(0, "helper_load_32",
					    VG_(fnptr_to_fnentry)(helper_load_32));
			cast_exp = IRExpr_Unop(Iop_32Uto64, exp);
			break;
		case Ity_I64:
		case Ity_F64:
			helper = mkIRCallee(0, "helper_load_64",
					    VG_(fnptr_to_fnentry)(helper_load_64));
			cast_exp = exp;
			break;
		case Ity_I128:
			helper = mkIRCallee(0, "helper_load_128",
					    VG_(fnptr_to_fnentry)(helper_load_128));
			args = mkIRExprVec_3(log_reads_expr(exp->Iex.Load.addr),
					     IRExpr_Unop(Iop_128to64, exp),
					     IRExpr_Unop(Iop_128HIto64, exp));
			break;
		case Ity_V128:
			helper = mkIRCallee(0, "helper_load_128",
					    VG_(fnptr_to_fnentry)(helper_load_128));
			args = mkIRExprVec_3(log_reads_expr(exp->Iex.Load.addr),
					     IRExpr_Unop(Iop_V128to64, exp),
					     IRExpr_Unop(Iop_V128HIto64, exp));
			break;
		}
		if (!args)
			args = mkIRExprVec_2(log_reads_expr(exp->Iex.Load.addr),
					     cast_exp);
		switch (exp->Iex.Load.ty) {
		case Ity_I32:
		case Ity_I64:
		case Ity_V128:
			return IRExpr_CCall(helper,
					    exp->Iex.Load.ty,
					    args);
		case Ity_I8:
			return IRExpr_Unop(Iop_64to8,
					   IRExpr_CCall(helper,
							Ity_I64,
							args));
		case Ity_I16:
			return IRExpr_Unop(Iop_64to16,
					   IRExpr_CCall(helper,
							Ity_I64,
							args));
		default:
			VG_(tool_panic)((signed char *)"Moo");
			return NULL;
		}
	}
	case Iex_Const:
		return exp;
	case Iex_CCall: {
		IRExpr **args;
		unsigned x;

		args = shallowCopyIRExprVec(exp->Iex.CCall.args);
		for (x = 0; args[x]; x++)
			args[x] = log_reads_expr(args[x]);
		return IRExpr_CCall(exp->Iex.CCall.cee,
				   exp->Iex.CCall.retty,
				   args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(log_reads_expr(exp->Iex.Mux0X.cond),
				   log_reads_expr(exp->Iex.Mux0X.expr0),
				   log_reads_expr(exp->Iex.Mux0X.exprX));
	}
	VG_(tool_panic)((signed char *)"Something bad");
}

static IRStmt *
log_write_stmt(IRExpr *addr, IRExpr *data, IRType typ)
{
	IRDirty *f;
	IRExpr **args;
	const char *helper_name;
	void *helper_addr;

	args = NULL;
	switch (typ) {
	case Ity_I8:
		helper_name = "helper_store_8";
		helper_addr = helper_store_8;
		data = IRExpr_Unop(Iop_8Uto64, data);
		break;
	case Ity_I16:
		helper_name = "helper_store_16";
		helper_addr = helper_store_16;
		data = IRExpr_Unop(Iop_16Uto64, data);
		break;
	case Ity_I32:
		helper_name = "helper_store_32";
		helper_addr = helper_store_32;
		data = IRExpr_Unop(Iop_32Uto64, data);
		break;
	case Ity_I64:
		helper_name = "helper_store_64";
		helper_addr = helper_store_64;
		break;
	case Ity_I128:
		helper_name = "helper_store_128";
		helper_addr = helper_store_128;
		args = mkIRExprVec_3(addr,
				     IRExpr_Unop(Iop_128to64, data),
				     IRExpr_Unop(Iop_128HIto64, data));
		break;
	case Ity_V128:
		helper_name = "helper_store_128";
		helper_addr = helper_store_128;
		args = mkIRExprVec_3(addr,
				     IRExpr_Unop(Iop_V128to64, data),
				     IRExpr_Unop(Iop_V128HIto64, data));
		break;
	default:
		VG_(tool_panic)((signed char *)"Bad write");
	}
	if (!args)
		args = mkIRExprVec_2(addr, data);
	f = unsafeIRDirty_0_N(0,
			      (HChar *)helper_name,
			      VG_(fnptr_to_fnentry)(helper_addr),
			      args);
	return IRStmt_Dirty(f);
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
		out_stmt = deepCopyIRStmt(current_in_stmt);
		switch (current_in_stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
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

			addStmtToIRSB(sb_out, IRStmt_Dirty(helper));
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put:
			out_stmt->Ist.Put.data = log_reads_expr(out_stmt->Ist.Put.data);
			break;
		case Ist_PutI:
			out_stmt->Ist.PutI.ix = log_reads_expr(out_stmt->Ist.PutI.ix);
			out_stmt->Ist.PutI.data = log_reads_expr(out_stmt->Ist.PutI.data);
			break;
		case Ist_WrTmp:
			out_stmt->Ist.WrTmp.data = log_reads_expr(out_stmt->Ist.WrTmp.data);
			break;
		case Ist_Store: {
			IRExpr *addr = current_in_stmt->Ist.Store.addr;
			IRExpr *data = current_in_stmt->Ist.Store.data;
			IRTemp addr_temp, data_temp;

			addr_temp = newIRTemp(sb_out->tyenv, Ity_I64);
			data_temp = newIRTemp(sb_out->tyenv,
					      typeOfIRExpr(sb_in->tyenv, data));
			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(addr_temp, log_reads_expr(addr)));
			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(data_temp, log_reads_expr(data)));
			addStmtToIRSB(sb_out,
				      log_write_stmt(IRExpr_RdTmp(addr_temp),
						     IRExpr_RdTmp(data_temp),
						     typeOfIRExpr(sb_in->tyenv,
								  current_in_stmt->Ist.Store.data)));
			out_stmt->Ist.Store.addr = IRExpr_RdTmp(addr_temp);
			out_stmt->Ist.Store.data = IRExpr_RdTmp(data_temp);
			break;
		}
		case Ist_CAS: {
			IRExpr *addr;
			IRExpr *dataLo;
			IRExpr *dataHi;
			IRCAS *details = out_stmt->Ist.CAS.details;
			IRType typ = typeOfIRExpr(sb_in->tyenv, details->dataLo);
			IRTemp addr_temp, dataLo_temp, dataHi_temp;

			addr = details->addr;
			dataLo = details->dataLo;
			dataHi = details->dataHi;

			addr_temp = newIRTemp(sb_out->tyenv, Ity_I64);
			dataLo_temp = newIRTemp(sb_out->tyenv,
						typeOfIRExpr(sb_out->tyenv,
							     dataLo));
			if (dataHi)
				dataHi_temp = newIRTemp(sb_out->tyenv,
							typeOfIRExpr(sb_out->tyenv,
								     dataHi));

			details->expdLo = log_reads_expr(details->expdLo);

			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(addr_temp,
						   log_reads_expr(addr)));
			details->addr = IRExpr_RdTmp(addr_temp);

			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(dataLo_temp,
						   log_reads_expr(dataLo)));
			details->dataLo = IRExpr_RdTmp(dataLo_temp);

			if (details->dataHi) {
				addStmtToIRSB(sb_out,
					      IRStmt_WrTmp(dataHi_temp,
							   log_reads_expr(dataHi)));
				details->dataHi = IRExpr_RdTmp(dataHi_temp);

				details->expdHi = log_reads_expr(details->expdHi);
			}

			addStmtToIRSB(sb_out,
				      log_write_stmt(addr, IRExpr_RdTmp(dataLo_temp),
						     typ));
			if (details->dataHi) {
				addStmtToIRSB(sb_out,
					      log_write_stmt(IRExpr_Binop(Iop_Add64,
									  IRExpr_RdTmp(addr_temp),
									  IRExpr_Const(IRConst_U64(sizeofIRType(typ)))),
							     IRExpr_RdTmp(dataHi_temp),
							     typ));
			}
			break;
		}
		case Ist_LLSC:
			VG_(printf)("Don't handle LLSC correctly.\n");
			break;
		case Ist_Dirty: {
			unsigned x;
			IRDirty *details;
			details = out_stmt->Ist.Dirty.details;
			details->guard = log_reads_expr(details->guard);
			for (x = 0; details->args[x]; x++)
				details->args[x] = log_reads_expr(details->args[x]);
			/* Not mAddr, because it's not actually read. */
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			out_stmt->Ist.Exit.guard =
				log_reads_expr(out_stmt->Ist.Exit.guard);
			break;
		}

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
