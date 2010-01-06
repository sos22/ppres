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

#define NONDETERMINISM_POISON 0xf001dead

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
	if (state->guest_RCX != fr->rcx &&
	    state->guest_RCX != NONDETERMINISM_POISON)
		VG_(printf)("Divergence on RCX (%llx vs %lx).\n",
			    state->guest_RCX, fr->rcx);
}

static int
replay_instr(VexGuestAMD64State *state, Word rip)
{
	struct record_header *rh;
	int r;

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
			r = replay_syscall(state);
			/* System calls clobber RCX.  Make it obvious
			   if that's a problem.  It shouldn't be for
			   programs which use the normal libc wrappers
			   around syscalls, which is the common case
			   (remember that we assume the client is
			   non-malicious). */
			state->guest_RCX = NONDETERMINISM_POISON;
			return r;

		case RECORD_memory:
			replay_memory(rh, (struct memory_record *)(rh + 1));
			finish_this_record(&logfile);
			break;
		case RECORD_rdtsc:
		case RECORD_mem_read:
		case RECORD_mem_write:
			/* Let the instruction run so as we can pick
			   the result up. */
			return 0;
		}
	}
}

static void
replay_load(void *ptr, unsigned size, const void *read_contents)
{
	struct record_header *rh;
	struct mem_read_record *mrr;

	rh = get_current_record(&logfile);
	tl_assert(rh->cls == RECORD_mem_read);
	mrr = (struct mem_read_record *)(rh + 1);
	if (ptr != mrr->ptr)
		VG_(printf)("Read from wrong place (%p vs %p)\n",
			    ptr, mrr->ptr);
	if (VG_(memcmp)(ptr, mrr + 1, size)) {
		if (size == 4) {
			if ( *(unsigned *)ptr != NONDETERMINISM_POISON )
				VG_(tool_panic)("Memory divergence!\n");
		} else if (size == 8) {
			if ( *(unsigned long *)ptr != NONDETERMINISM_POISON )
				VG_(tool_panic)("Memory divergence!\n");
		} else {
			VG_(tool_panic)("Memory divergence!\n");
		}
	}
	finish_this_record(&logfile);
}

static void
replay_store(void *ptr, unsigned size, const void *written_bytes)
{
	struct record_header *rh;
	struct mem_write_record *mrr;

	rh = get_current_record(&logfile);
	tl_assert(rh->cls == RECORD_mem_write);
	mrr = (struct mem_write_record *)(rh + 1);
	if (ptr != mrr->ptr)
		VG_(printf)("Wrote to wrong place (%p vs %p)\n",
			    ptr, mrr->ptr);
	finish_this_record(&logfile);
}

#define mk_helper_load(typ, suffix)                    \
static typ                                             \
helper_load_ ## suffix (void *ptr, typ val)            \
{                                                      \
	replay_load(ptr, sizeof(val), &val);           \
	return val;                                    \
}

#define mk_helper_store(typ, suffix)                   \
static void                                            \
helper_store_ ## suffix (void *ptr, typ val)           \
{                                                      \
	replay_store(ptr, sizeof(val), &val);          \
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
	IRStmt *tmp_stmt;
	unsigned i;
	IRDirty *helper;
	IRTemp helper_did_instruction;

	sb_out = deepCopyIRSBExceptStmts(sb_in);
	for (i = 0; i < sb_in->stmts_used; i++) {
		current_in_stmt = sb_in->stmts[i];
		out_stmt = deepCopyIRStmt(current_in_stmt);
		switch (current_in_stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
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

			addStmtToIRSB(sb_out, IRStmt_Dirty(helper));

			tmp_stmt = IRStmt_Exit(
				IRExpr_Binop(Iop_CmpNE8,
					     IRExpr_Const(IRConst_U8(0)),
					     IRExpr_RdTmp(helper_did_instruction)),
				Ijk_Boring,
				IRConst_U64(
					current_in_stmt->Ist.IMark.addr +
					current_in_stmt->Ist.IMark.len));
			addStmtToIRSB(sb_out, tmp_stmt);
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
			VG_(printf)("Don't handle LLSC\n");
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
