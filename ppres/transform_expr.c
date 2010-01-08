/* This gets #include'd into both the replay and record systems.  It
  contains all the gubbins needed to add the monitoring infrastructure
  to VEX IR. */

#ifdef included_for_replay
# define load_worker_function replay_load
# define store_worker_function replay_store
#else
# ifndef included_for_record
#  error Neither record nor replay?
# endif
# define load_worker_function record_load
# define store_worker_function record_store
#endif

#define mk_helper_load(typ, suffix)                    \
static typ                                             \
helper_load_ ## suffix (void *ptr)                     \
{                                                      \
        typ val;                                       \
	load_worker_function(ptr, sizeof(val), &val);  \
	return val;                                    \
}

#define mk_helper_store(typ, suffix)                   \
static void                                            \
helper_store_ ## suffix (void *ptr, typ val)           \
{                                                      \
	store_worker_function(ptr, sizeof(val), &val); \
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
log_reads_expr(IRSB *sb, IRExpr *exp)
{
	switch (exp->tag) {
	case Iex_Get:
	case Iex_Binder:
	case Iex_RdTmp:
		return exp;
	case Iex_GetI:
		return IRExpr_GetI(exp->Iex.GetI.descr,
				   log_reads_expr(sb, exp->Iex.GetI.ix),
				   exp->Iex.GetI.bias);
	case Iex_Qop:
		return IRExpr_Qop(exp->Iex.Qop.op,
				  log_reads_expr(sb, exp->Iex.Qop.arg1),
				  log_reads_expr(sb, exp->Iex.Qop.arg2),
				  log_reads_expr(sb, exp->Iex.Qop.arg3),
				  log_reads_expr(sb, exp->Iex.Qop.arg4));
	case Iex_Triop:
		return IRExpr_Triop(exp->Iex.Triop.op,
				    log_reads_expr(sb, exp->Iex.Triop.arg1),
				    log_reads_expr(sb, exp->Iex.Triop.arg2),
				    log_reads_expr(sb, exp->Iex.Triop.arg3));
	case Iex_Binop:
		return IRExpr_Binop(exp->Iex.Binop.op,
				    log_reads_expr(sb, exp->Iex.Binop.arg1),
				    log_reads_expr(sb, exp->Iex.Binop.arg2));
	case Iex_Unop:
		return IRExpr_Unop(exp->Iex.Unop.op,
				   log_reads_expr(sb, exp->Iex.Unop.arg));
	case Iex_Load: {
		IRExpr **args;
		void *helper;
		const char *helper_name;
		IRTemp dest;
		IRDirty *f;

#define HLP(x) helper_name = "helper_load_" #x ; helper = helper_load_ ## x ;
		switch (exp->Iex.Load.ty) {
		case Ity_INVALID:
			VG_(tool_panic)((signed char *)"Bad type 1");;
		case Ity_I1:
			VG_(tool_panic)((signed char *)"Bad type 2");
		case Ity_I8:
			HLP(8);
			break;
		case Ity_I16:
			HLP(16);
			break;
		case Ity_I32:
		case Ity_F32:
			HLP(32);
			break;
		case Ity_I64:
		case Ity_F64:
			HLP(64);
			break;
		case Ity_I128:
			HLP(128);
			break;
		case Ity_V128:
			HLP(128);
			break;
		}

		args = mkIRExprVec_1(log_reads_expr(sb, exp->Iex.Load.addr));
		dest = newIRTemp(sb->tyenv, exp->Iex.Load.ty);
		f = unsafeIRDirty_1_N(dest,
				      0,
				      (HChar *)helper_name,
				      VG_(fnptr_to_fnentry)(helper),
				      args);
		addStmtToIRSB(sb, IRStmt_Dirty(f));
		return IRExpr_RdTmp(dest);
	}
	case Iex_Const:
		return exp;
	case Iex_CCall: {
		IRExpr **args;
		unsigned x;

		args = shallowCopyIRExprVec(exp->Iex.CCall.args);
		for (x = 0; args[x]; x++)
			args[x] = log_reads_expr(sb, args[x]);
		return IRExpr_CCall(exp->Iex.CCall.cee,
				    exp->Iex.CCall.retty,
				    args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(log_reads_expr(sb, exp->Iex.Mux0X.cond),
				    log_reads_expr(sb, exp->Iex.Mux0X.expr0),
				    log_reads_expr(sb, exp->Iex.Mux0X.exprX));
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
#if SEARCH_USES_FOOTSTEPS || defined(included_for_record)
			helper = unsafeIRDirty_0_N(
				0,
#ifdef included_for_replay
				"footstep_event",
				VG_(fnptr_to_fnentry)(footstep_event),
#else
				"record_instr",
				VG_(fnptr_to_fnentry)(record_instr),
#endif
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
			out_stmt->Ist.Put.data = log_reads_expr(sb_out, out_stmt->Ist.Put.data);
			break;
		case Ist_PutI:
			out_stmt->Ist.PutI.ix = log_reads_expr(sb_out, out_stmt->Ist.PutI.ix);
			out_stmt->Ist.PutI.data = log_reads_expr(sb_out, out_stmt->Ist.PutI.data);
			break;
		case Ist_WrTmp:
			out_stmt->Ist.WrTmp.data = log_reads_expr(sb_out, out_stmt->Ist.WrTmp.data);
			break;
		case Ist_Store: {
			IRExpr *addr = current_in_stmt->Ist.Store.addr;
			IRExpr *data = current_in_stmt->Ist.Store.data;
			IRTemp addr_temp, data_temp;

			addr_temp = newIRTemp(sb_out->tyenv, Ity_I64);
			data_temp = newIRTemp(sb_out->tyenv,
					      typeOfIRExpr(sb_in->tyenv, data));
			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(addr_temp, log_reads_expr(sb_out, addr)));
			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(data_temp, log_reads_expr(sb_out, data)));
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

			details->expdLo = log_reads_expr(sb_out, details->expdLo);

			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(addr_temp,
						   log_reads_expr(sb_out, addr)));
			details->addr = IRExpr_RdTmp(addr_temp);

			addStmtToIRSB(sb_out,
				      IRStmt_WrTmp(dataLo_temp,
						   log_reads_expr(sb_out, dataLo)));
			details->dataLo = IRExpr_RdTmp(dataLo_temp);

			if (details->dataHi) {
				addStmtToIRSB(sb_out,
					      IRStmt_WrTmp(dataHi_temp,
							   log_reads_expr(sb_out, dataHi)));
				details->dataHi = IRExpr_RdTmp(dataHi_temp);

				details->expdHi = log_reads_expr(sb_out, details->expdHi);
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
			details->guard = log_reads_expr(sb_out, details->guard);
			for (x = 0; details->args[x]; x++)
				details->args[x] = log_reads_expr(sb_out, details->args[x]);
			/* Not mAddr, because it's not actually read. */
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			out_stmt->Ist.Exit.guard =
				log_reads_expr(sb_out, out_stmt->Ist.Exit.guard);
			break;
		}
		addStmtToIRSB(sb_out, out_stmt);
	}

#ifdef included_for_replay
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
#endif

	return sb_out;
}
