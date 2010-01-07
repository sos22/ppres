/* The replay engine itself.  We structure this as, effectively, a
   pair of co-routines.  One of the co-routines runs the client code
   and the other one runs the replay engine state machine. */
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
#include "coroutines.h"

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

struct replay_thread {
	struct replay_thread *next_thread;
	struct coroutine coroutine;
	ThreadId id;
	Bool in_generated;
};

static struct coroutine
replay_state_machine;
static struct replay_thread *
head_thread, *
current_thread;

static Bool
search_mode;
static int
search_mode_output_fd;

#define CSR_BUFFER 16

static struct {
	enum {CLIENT_STOP_footstep,
	      CLIENT_STOP_syscall,
	      CLIENT_STOP_rdtsc,
	      CLIENT_STOP_mem_read,
	      CLIENT_STOP_mem_write} cls;
	VexGuestAMD64State *state;
	union {
		struct {
			void *ptr;
			unsigned size;
			unsigned char buffer[CSR_BUFFER];
		} mem_read;
		struct {
			void *ptr;
			unsigned size;
			unsigned char buffer[CSR_BUFFER];
		} mem_write;
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


static struct {
	unsigned long rdtsc;
} client_resume;

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

void
coroutine_bad_return_c(const char *name)
{
	VG_(printf)("Coroutine returned unexpectedly!\n");
	VG_(printf)("(%s)\n", name);
	VG_(tool_panic)("Coroutine error");
}

static void
run_client(struct replay_thread *who)
{
	current_thread = who;
	run_coroutine(&replay_state_machine, &who->coroutine);
}

static void
run_replay_machine(void)
{
	struct replay_thread *whom;
	whom = current_thread;
	current_thread->in_generated = VG_(in_generated_code);
	run_coroutine(&whom->coroutine, &replay_state_machine);
	tl_assert(current_thread == whom);
	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = current_thread->in_generated;
}

static void
footstep_event(VexGuestAMD64State *state, Addr rip)
{
	client_stop_reason.cls = CLIENT_STOP_footstep;
	client_stop_reason.state = state;
	state->guest_RIP = rip;
	run_replay_machine();
}

static void
syscall_event(VexGuestAMD64State *state)
{
	client_stop_reason.cls = CLIENT_STOP_syscall;
	client_stop_reason.state = state;
	run_replay_machine();
}

static void
replay_load(void *ptr, unsigned size, const void *read_contents)
{
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
	client_stop_reason.cls = CLIENT_STOP_mem_write;
	client_stop_reason.u.mem_write.ptr = ptr;
	client_stop_reason.u.mem_write.size = size;
	VG_(memcpy)(client_stop_reason.u.mem_write.buffer,
		    written_bytes,
		    size);
	run_replay_machine();
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
				0,
				"footstep_event",
				VG_(fnptr_to_fnentry)(footstep_event),
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

			addStmtToIRSB(sb_out, out_stmt);
			out_stmt = IRStmt_Dirty(helper);
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

	if (sb_out->jumpkind == Ijk_Sys_syscall) {
		helper = unsafeIRDirty_0_N(
			0,
			"syscall_event",
			VG_(fnptr_to_fnentry)(syscall_event),
			mkIRExprVec_0());

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
		sb_out->jumpkind = Ijk_Boring;
	}
	tl_assert(sb_out->jumpkind == Ijk_Boring ||
		  sb_out->jumpkind == Ijk_Call ||
		  sb_out->jumpkind == Ijk_Ret);

	return sb_out;
}

static struct replay_thread *
get_thread(ThreadId id)
{
	struct replay_thread *rt;

	for (rt = head_thread; rt && rt->id != id; rt = rt->next_thread)
		;
	tl_assert(rt != NULL);
	return rt;
}

static void
replay_footstep_record(struct footstep_record *fr,
		       struct record_header *rh)
{
	run_client(get_thread(rh->tid));
	tl_assert(client_stop_reason.cls == CLIENT_STOP_footstep);
	tl_assert(client_stop_reason.state->guest_RIP == fr->rip);
	tl_assert(client_stop_reason.state->guest_RAX == fr->rax);
	tl_assert(client_stop_reason.state->guest_RDX == fr->rdx);
	tl_assert(client_stop_reason.state->guest_RCX == fr->rcx ||
		  client_stop_reason.state->guest_RCX == NONDETERMINISM_POISON);
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
replay_syscall_record(struct syscall_record *sr)
{
	run_client(current_thread);

	tl_assert(client_stop_reason.cls == CLIENT_STOP_syscall);
	tl_assert(client_stop_reason.state->guest_RAX == sr->syscall_nr);

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
	case __NR_exit_group:
	case __NR_set_robust_list:
	case __NR_rt_sigaction:
	case __NR_rt_sigprocmask:
	case __NR_exit:
	case __NR_futex: /* XXX not quite right, but good enough for
			  * now. */

		VG_(client_syscall)(VG_(get_running_tid)(),
				    VEX_TRC_JMP_SYS_SYSCALL);
		if (sr_isError(sr->syscall_res))
			tl_assert(-client_stop_reason.state->guest_RAX ==
				  sr_Err(sr->syscall_res));
		else
			tl_assert(client_stop_reason.state->guest_RAX ==
				  sr_Res(sr->syscall_res));
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

	default:
		VG_(printf)("don't know how to replay syscall %lld yet\n",
			    client_stop_reason.state->guest_RAX);
		VG_(exit)(1);
	}
}

static void
replay_rdtsc_record(struct rdtsc_record *rr)
{
	run_client(current_thread);

	tl_assert(client_stop_reason.cls == CLIENT_STOP_rdtsc);
	client_resume.rdtsc = rr->stashed_tsc;

	finish_this_record(&logfile);
}

static void
replay_mem_read_record(struct record_header *rh,
		       struct mem_read_record *mrr)
{
	unsigned recorded_read_size;
	void *recorded_read;
	int safe;

	run_client(current_thread);

	tl_assert(client_stop_reason.cls == CLIENT_STOP_mem_read);
	tl_assert(client_stop_reason.u.mem_read.ptr == mrr->ptr);
	recorded_read_size = rh->size - sizeof(*rh) - sizeof(*mrr);
	recorded_read = mrr + 1;
	tl_assert(client_stop_reason.u.mem_read.size == recorded_read_size);
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
		VG_(tool_panic)((signed char *)"Memory divergence!");
	finish_this_record(&logfile);
}

static void
replay_mem_write_record(struct record_header *rh,
			struct mem_write_record *mwr)
{
	unsigned recorded_write_size;
	void *recorded_write;
	int safe;

	run_client(current_thread);

	tl_assert(client_stop_reason.cls == CLIENT_STOP_mem_write);
	tl_assert(client_stop_reason.u.mem_write.ptr == mwr->ptr);
	recorded_write_size = rh->size - sizeof(*rh) - sizeof(*mwr);
	recorded_write = mwr + 1;
	tl_assert(client_stop_reason.u.mem_write.size == recorded_write_size);
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
		VG_(tool_panic)((signed char *)"Memory divergence!");
	finish_this_record(&logfile);
}

static void
replay_state_machine_fn(void)
{
	struct record_header *rh;
	void *payload;

	VG_(printf)("Replay state machine starting...\n");
	while (1) {
		rh = get_current_record(&logfile);
		payload = rh + 1;
		if (rh->tid != VG_(get_running_tid)())
			VG_(printf)("Ooops: thread %d != %d\n",
				    rh->tid, VG_(get_running_tid)());
		switch (rh->cls) {
		case RECORD_footstep:
			replay_footstep_record(payload, rh);
			break;
		case RECORD_syscall:
			replay_syscall_record(payload);
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
		default:
			VG_(tool_panic)((signed char *)"Unknown replay record type!");
		}
	}
}

static struct replay_thread *
spawning_thread;

static void
init_replay_machine(void)
{
	open_logfile(&logfile, (signed char *)"logfile1");

	/* Run the state machine.  It should come back here to get the
	   first instruction of the program executed. */
	VG_(printf)("Invoking replay state machine.\n");
	current_thread = head_thread;
	run_coroutine(&head_thread->coroutine, &replay_state_machine);
	VG_(printf)("Replay state machine activated client.\n");
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
	int fds[2];
	unsigned char buf;

	make_coroutine(&replay_state_machine,
		       "replay_state_machine",
		       replay_state_machine_stack,
		       sizeof(replay_state_machine_stack),
		       replay_state_machine_fn,
		       0);

	head_thread = VG_(malloc)("head_thread", sizeof(*head_thread));
	VG_(memset)(head_thread, 0, sizeof(*head_thread));
	head_thread->id = 1;

	VG_(pipe)(fds);
	if (my_fork() == 0) {
		/* We're the searcher process, and we need to go and
		   find the execution schedule. */
		VG_(close)(fds[0]);
		search_mode = True;
		search_mode_output_fd = fds[1];
		VG_(printf)("Running search phase.\n");
	} else {
		/* We're the validation process.  Grab the schedule
		   from the child. */
		VG_(close)(fds[1]);
		while (VG_(read)(fds[0], &buf, sizeof(buf)))
			;
		VG_(close)(fds[0]);
		VG_(printf)("Running validation phase.\n");
	}
	init_replay_machine();
}

static void
fini(Int ignore)
{
	close_logfile(&logfile);
	if (search_mode) {
		/* Schedules are currently dummy structures. */
		VG_(close)(search_mode_output_fd);
		VG_(printf)("Finished search phase.\n");
	} else {
		VG_(printf)("Finished validation phase.\n");
	}
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

	VG_(printf)("Running new child briefly.\n");
	VG_(running_tid) = VG_INVALID_THREADID;
	local_thread = current_thread;
	VG_(in_generated_code) = False;
	run_client(spawning_thread);
	current_thread = local_thread;
	VG_(running_tid) = current_thread->id;
	VG_(printf)("Back from child.\n");

	rt->next_thread = head_thread;
	head_thread = rt;

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
