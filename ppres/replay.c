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

/* Which records are we allowed to look at when doing searches? */
#define SEARCH_USES_FOOTSTEPS 0

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
static struct execution_schedule
execution_schedule;

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
	VG_(tool_panic)((Char *)"Coroutine error");
}

/* Switch from the monitor to client code in thread @who (which might
   be the current thread).  The client might do a thread switch
   itself, so we can be anywhere when we come back. */
static void
run_client(struct replay_thread *who)
{
	if (who != current_thread)
		VG_(printf)("Monitor goes to thread %d\n",
			    who->id);

	current_thread->in_generated = VG_(in_generated_code);
	current_thread = who;

	run_coroutine(&replay_state_machine, &who->coroutine);
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
	run_coroutine(&whom->coroutine, &replay_state_machine);
	tl_assert(current_thread == whom);
	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = current_thread->in_generated;
}

static void
reschedule_core(struct coroutine *my_coroutine)
{
	struct replay_thread *rt, *me;
	unsigned other_threads;
	unsigned thread_to_run;
	unsigned x;

	me = current_thread;
	other_threads = 0;
	rt = head_thread;
	while (rt != NULL) {
		if (rt != me)
			other_threads++;
		rt = rt->next_thread;
	}

	thread_to_run = make_nd_choice(&execution_schedule,
				       other_threads);
	tl_assert(thread_to_run <= other_threads);
	if (thread_to_run == 0) {
		/* Keep running this thread. */
		return;
	}

	rt = head_thread;
	if (rt == me)
		rt = rt->next_thread;
	x = 1;
	while (x < thread_to_run) {
		rt = rt->next_thread;
		if (rt == me)
			rt = rt->next_thread;
		x++;
	}

	VG_(printf)("Switch to thread %d\n", rt->id);
	me->in_generated = VG_(in_generated_code);
	current_thread = rt;
	run_coroutine(my_coroutine, &rt->coroutine);
	VG_(printf)("Switch back again to %d\n", me->id);
	current_thread = me;
	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = current_thread->in_generated;
}

static void
reschedule_replay_monitor(void)
{
	reschedule_core(&replay_state_machine);
}

static void
reschedule(void)
{
	reschedule_core(&current_thread->coroutine);
}

#if SEARCH_USES_FOOTSTEPS
static void
footstep_event(VexGuestAMD64State *state, Addr rip)
{
	reschedule();
	client_stop_reason.cls = CLIENT_STOP_footstep;
	client_stop_reason.state = state;
	state->guest_RIP = rip;
	run_replay_machine();
	reschedule();
}
#endif

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
	reschedule();
	client_stop_reason.cls = CLIENT_STOP_mem_read;
	client_stop_reason.u.mem_read.ptr = ptr;
	client_stop_reason.u.mem_read.size = size;
	VG_(memcpy)(client_stop_reason.u.mem_read.buffer,
		    read_contents,
		    size);
	run_replay_machine();
	reschedule();
}

static void
replay_store(void *ptr, unsigned size, const void *written_bytes)
{
	reschedule();
	client_stop_reason.cls = CLIENT_STOP_mem_write;
	client_stop_reason.u.mem_write.ptr = ptr;
	client_stop_reason.u.mem_write.size = size;
	VG_(memcpy)(client_stop_reason.u.mem_write.buffer,
		    written_bytes,
		    size);
	run_replay_machine();
	reschedule();
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
#if SEARCH_USES_FOOTSTEPS
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
#endif
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

static long
my__exit(int code)
{
	long res;
	asm ("syscall"
	     : "=a" (res)
	     : "0" (__NR_exit), "rdi" (code));
	return res;
}

static void
failure(const char *fmt, ...)
{
	va_list args;
	VG_(printf)("Replay failed after %ld bytes\n",
		    logfile.offset_in_file);
	va_start(args, fmt);
	VG_(vprintf)(fmt, args);
	my__exit(1);
}

#define replay_assert(cond, msg, ...)                     \
do {                                                      \
	if (!(cond))                                      \
		failure("Assertion %s failed: " msg "\n", \
                        #cond , ## __VA_ARGS__);          \
} while (0)

static void
replay_footstep_record(struct footstep_record *fr,
		       struct record_header *rh)
{
#if SEARCH_USES_FOOTSTEPS
#if 0
	run_client(get_thread(rh->tid));
#else
	run_client(current_thread);
	replay_assert(rh->tid == current_thread->id,
		      "was in thread %d, wanted thread %d",
		      current_thread->id, rh->tid);
#endif
	replay_assert(client_stop_reason.cls == CLIENT_STOP_footstep,
		      "wanted a footstep, got class %d",
		      client_stop_reason.cls);
	replay_assert(client_stop_reason.state->guest_RIP == fr->rip,
		      "wanted a footstep at %lx, got one at %lx",
		      fr->rip, client_stop_reason.state->guest_RIP);
	replay_assert(client_stop_reason.state->guest_RAX == fr->rax,
		      "RAX mismatch");
	replay_assert(client_stop_reason.state->guest_RDX == fr->rdx,
		      "RDX mismatch");
	replay_assert(client_stop_reason.state->guest_RCX == fr->rcx ||
		      client_stop_reason.state->guest_RCX == NONDETERMINISM_POISON,
		      "RCX mismatch");
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
replay_syscall_record(struct syscall_record *sr)
{
	run_client(current_thread);

	replay_assert(client_stop_reason.cls == CLIENT_STOP_syscall,
		      "wanted a syscall, got class %d",
		      client_stop_reason.cls);
	replay_assert(client_stop_reason.state->guest_RAX == sr->syscall_nr,
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
	case __NR_futex: /* XXX not quite right, but good enough for
			  * now. */

		VG_(client_syscall)(VG_(get_running_tid)(),
				    VEX_TRC_JMP_SYS_SYSCALL);
		if (sr_isError(sr->syscall_res))
			replay_assert(-client_stop_reason.state->guest_RAX ==
				      sr_Err(sr->syscall_res),
				      "Expected syscall to fail %d, actually got %d",
				      sr_Err(sr->syscall_res),
				      -client_stop_reason.state->guest_RAX);
		else
			replay_assert(client_stop_reason.state->guest_RAX ==
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

	replay_assert(client_stop_reason.cls == CLIENT_STOP_rdtsc,
		      "wanted a rdtsc, got class %d",
		      client_stop_reason.cls);
	client_resume.rdtsc = rr->stashed_tsc;

	finish_this_record(&logfile);
}

#define MAGIC_PTR (void *)0x601030

static void
replay_mem_read_record(struct record_header *rh,
		       struct mem_read_record *mrr)
{
	unsigned recorded_read_size;
	void *recorded_read;
	int safe;

	run_client(current_thread);

	replay_assert(current_thread->id == rh->tid,
		      "wanted to be in thread %d, was in %d",
		      rh->tid,
		      current_thread->id);
	replay_assert(client_stop_reason.cls == CLIENT_STOP_mem_read,
		      "wanted a memory read, got class %d",
		      client_stop_reason.cls);
	replay_assert(client_stop_reason.u.mem_read.ptr == mrr->ptr,
		      "Expected a read from %p, got one from %p",
		      mrr->ptr,
		      client_stop_reason.u.mem_read.ptr);

	recorded_read_size = rh->size - sizeof(*rh) - sizeof(*mrr);
	recorded_read = mrr + 1;
	replay_assert(client_stop_reason.u.mem_read.size == recorded_read_size,
		      "wanted read of size %d, got size %d",
		      recorded_read_size, client_stop_reason.u.mem_read.size);

	if (mrr->ptr == MAGIC_PTR)
		VG_(printf)("Thread %d(%d) reads %x\n",
			    current_thread->id,
			    rh->tid,
			    *(unsigned *)client_stop_reason.u.mem_read.buffer);

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
		VG_(tool_panic)("Memory divergence!");
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

	replay_assert(current_thread->id == rh->tid,
		      "wanted to be in thread %d, was in %d for write",
		      rh->tid,
		      current_thread->id);
	replay_assert(client_stop_reason.cls == CLIENT_STOP_mem_write,
		      "wanted a memory write, got class %d",
		      client_stop_reason.cls);
	replay_assert(client_stop_reason.u.mem_write.ptr == mwr->ptr,
		      "Expected a write to %p, got one to %p",
		      mwr->ptr,
		      client_stop_reason.u.mem_read.ptr);
	recorded_write_size = rh->size - sizeof(*rh) - sizeof(*mwr);
	recorded_write = mwr + 1;
	replay_assert(client_stop_reason.u.mem_write.size == recorded_write_size,
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
		VG_(tool_panic)("Memory divergence!");
	finish_this_record(&logfile);
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
		payload = rh + 1;
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
	int status;

	/* Search for a valid execution schedule. */
	create_empty_execution_schedule(schedule);

	while (1) {
		child = my_fork();
		if (child == 0) {
			/* We're the child process, and so we need to
			   go and do the exploration. */
			break;
		}
		/* We're the parent.  See how far that child gets. */
		VG_(waitpid)(child, &status, 0);
		if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
			/* Child said that everything's okay.
			 * Woohoo. */
			VG_(printf)("Found a valid schedule.\n");
			my__exit(0);
		}
		/* That schedule didn't work.  Try another one. */
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
success(void)
{
	close_logfile(&logfile);
	VG_(printf)("Finished search phase.\n");
	my__exit(0);
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
	run_client(spawning_thread);
	current_thread = local_thread;
	VG_(running_tid) = current_thread->id;
	VG_(in_generated_code) = True;

	rt->next_thread = head_thread;
	head_thread = rt;

	reschedule_replay_monitor();

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
