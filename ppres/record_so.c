#include <asm/prctl.h>
#include <sys/prctl.h>
#include <setjmp.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>

#include <libvex.h>
#include <libvex_guest_amd64.h>
#include <libvex_trc_values.h>
#include <pub_tool_basics.h>
#include <pub_tool_libcbase.h>
#include <pub_tool_libcassert.h>
#include <pub_tool_libcprint.h>
#include <pub_tool_vki.h>
#include <pub_tool_mallocfree.h>
#include <pub_tool_options.h>
#include <pub_tool_tooliface.h>
#include <pub_tool_xarray.h>

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"
#include "../coregrind/pub_core_threadstate.h"
#include "../coregrind/pub_core_tooliface.h"
#include "../coregrind/pub_core_libcsignal.h"
#include "../coregrind/pub_core_debuglog.h"
#include "../coregrind/pub_core_aspacemgr.h"
#include "../coregrind/pub_core_scheduler.h"
#include "../coregrind/pub_core_syswrap.h"
#include "../coregrind/pub_core_signals.h"
#include "../coregrind/pub_core_dispatch_asm.h"
#include "../coregrind/m_scheduler/priv_sema.h"
#include "../coregrind/pub_core_clientstate.h"

int arch_prctl(int code, unsigned long *addr);
void setup_file_descriptors(void);
extern UInt VG_(dispatch_ctr);
extern vg_sema_t the_BigLock;

unsigned char interim_stack[16384];

struct fpu_save {
    unsigned short control;
    unsigned short pad0;
    unsigned short status;
    unsigned short pad1;
    unsigned short tag;
    unsigned short pad2;
    unsigned int ip;
    unsigned short cs;
    unsigned opcode:11;
    unsigned pad3:5;
    unsigned operand;
    unsigned short ds;
    unsigned short pad4;
    unsigned char registers[80];
};

/* Set the standard set of blocked signals, used whenever we're not
   running a client syscall. */
static void block_signals(void)
{
   vki_sigset_t mask;

   VG_(sigfillset)(&mask);

   /* Don't block these because they're synchronous */
   VG_(sigdelset)(&mask, VKI_SIGSEGV);
   VG_(sigdelset)(&mask, VKI_SIGBUS);
   VG_(sigdelset)(&mask, VKI_SIGFPE);
   VG_(sigdelset)(&mask, VKI_SIGILL);
   VG_(sigdelset)(&mask, VKI_SIGTRAP);

   /* Can't block these anyway */
   VG_(sigdelset)(&mask, VKI_SIGSTOP);
   VG_(sigdelset)(&mask, VKI_SIGKILL);

   VG_(sigprocmask)(VKI_SIG_SETMASK, &mask, NULL);
}

static void
initialise_valgrind(unsigned long initial_rsp)
{
    Bool ok;

    VG_(brk_base) = (ULong)sbrk(0);
    VG_(brk_limit) = VG_(brk_base);

    VG_(debugLog_startup)(0, "Stage 2 (main)");

    VG_(am_startup)(initial_rsp);

    VG_(tl_pre_clo_init)();
    VG_TDICT_CALL(tool_post_clo_init);

    setup_file_descriptors();

    ML_(sema_init)(&the_BigLock);

    ok = VG_(am_create_reservation)(
	VG_(brk_base),
	8 * 1024 * 1024 - VKI_PAGE_SIZE,
	SmLower,
	VKI_PAGE_SIZE);
    if (!ok)
	VG_(printf)("Whoops: can't create brk segment\n");
    VG_(am_mmap_anon_fixed_client)(VG_(brk_base), VKI_PAGE_SIZE,
				   VKI_PROT_READ|VKI_PROT_WRITE|VKI_PROT_EXEC);

    LibVEX_default_VexControl(& VG_(clo_vex_control));
}

static void
run_thread(unsigned long initial_rsp, unsigned long initial_rip)
{
    ThreadState *tas;
    unsigned mxcsr;
    struct fpu_save fpu_save;
    VexGuestArchState *gas;
    unsigned x;
    ThreadId tid;

    tid = VG_(alloc_ThreadState)();
    tas = &VG_(threads)[tid];
    gas = &tas->arch.vex;

    gas->guest_RSP = initial_rsp;
    gas->guest_RIP = initial_rip;
    arch_prctl(ARCH_GET_FS, &gas->guest_FS_ZERO);

    asm ("stmxcsr %0\n"
	 : "=m" (mxcsr));

    gas->guest_SSEROUND = (mxcsr >> 13) & 3;

    /* Save XMM registers.  Done in two statements to make things a
       bit easier on gcc. */
    asm (
#define DO_REG(x) "movdqu %%xmm" #x ", %" #x "\n"
	DO_REG(0)
	DO_REG(1)
	DO_REG(2)
	DO_REG(3)
	DO_REG(4)
	DO_REG(5)
	DO_REG(6)
	DO_REG(7)
#undef DO_REG
#define DO_REG(x) "=m" (gas->guest_XMM ## x)
	: DO_REG(0),
	  DO_REG(1),
	  DO_REG(2),
	  DO_REG(3),
	  DO_REG(4),
	  DO_REG(5),
	  DO_REG(6),
	  DO_REG(7)
#undef DO_REG
	);
    asm (
#define DO_REG(x,y) "movdqu %%xmm" #x ", %" #y "\n"
	DO_REG(8,0)
	DO_REG(9,1)
	DO_REG(10,2)
	DO_REG(11,3)
	DO_REG(12,4)
	DO_REG(13,5)
	DO_REG(14,6)
	DO_REG(15,7)
#undef DO_REG
#define DO_REG(x) "=m" (gas->guest_XMM ## x)
	: DO_REG(8),
	  DO_REG(9),
	  DO_REG(10),
	  DO_REG(11),
	  DO_REG(12),
	  DO_REG(13),
	  DO_REG(14),
	  DO_REG(15)
#undef DO_REG
	);

    memset(&fpu_save, 0, sizeof(fpu_save));
    asm("fsave %0"
	: "=m" (fpu_save));
    gas->guest_FTOP = (fpu_save.status >> 10) & 7;
    for (x = 0; x < gas->guest_FTOP; x++)
	asm("fdecstp\n");
    asm("fst %0\n"
#define DO_REG(x) "fst %%st(" #x ")\nfst %" #x "\n"
	DO_REG(1)
	DO_REG(2)
	DO_REG(3)
	DO_REG(4)
	DO_REG(5)
	DO_REG(6)
	DO_REG(7)
#undef DO_REG
	: "=m" (gas->guest_FPREG[0]),
	  "=m" (gas->guest_FPREG[1]),
	  "=m" (gas->guest_FPREG[2]),
	  "=m" (gas->guest_FPREG[3]),
	  "=m" (gas->guest_FPREG[4]),
	  "=m" (gas->guest_FPREG[5]),
	  "=m" (gas->guest_FPREG[6]),
	  "=m" (gas->guest_FPREG[7]));
    for (x = 0; x < 8; x++)
	gas->guest_FPTAG[x] = (fpu_save.tag >> (x * 2)) & 3;
    gas->guest_FPROUND = (fpu_save.control >> 9) & 3;
    gas->guest_FC3210 = ((fpu_save.status >> 8) & 7) |
	((fpu_save.status >> 11) & 8);

    VG_(acquire_BigLock)(tid, "thread starts");
    VG_(dispatch_ctr) = 10000;
    while (!VG_(is_exiting)(tid)) {
	int r;

	r = VG_(run_innerloop)(&tas->arch, 0);
	switch (r) {
	case VEX_TRC_JMP_SYS_SYSCALL: {
	    VG_(printf)("Client syscall\n");
	    Bool jumped =  __builtin_setjmp(tas->sched_jmpbuf);
	    if (!jumped) {
		tas->sched_jmpbuf_valid = True;
		VG_(client_syscall)(tid, r);
	    }
	    tas->sched_jmpbuf_valid = False;
	    if (jumped) {
		block_signals();
		VG_(poll_signals)(tid);
	    }
	    break;
	}

	case VG_TRC_INNER_COUNTERZERO:
	    VG_(release_BigLock)(tid, VgTs_Yielding,
				 "scheduler timeslice");
	    VG_(acquire_BigLock)(tid, "scheduler timeslice");
	    VG_(poll_signals)(tid);
	    VG_(dispatch_ctr) = 10000;
	    break;

	default:
	    VG_(printf)("Unknown VEX trace return %d\n", r);
	    VG_(tool_panic)((Char *)"dead");
	}
    }
}

void
start_interpreting(unsigned long initial_rsp, unsigned long initial_rip)
{
    initialise_valgrind(initial_rsp);

    run_thread(initial_rsp, initial_rip);

    VG_(printf)("Thread exitted?\n");
}

void
_init()
{
    unsigned long ign;

    printf("init() called\n");

    asm ("pushq %%rbp\n"
	 "lea 1f(%%rip), %%rsi\n"
	 "xchg %%rsp, %%rdi\n"
	 "call start_interpreting@PLT\n"

	 "1:\n" /* We never actually run this, but it's the first
		   thing which gets interpreted. */
	 "popq %%rbp\n"
	 : "=D" (ign)
	 : "0" (interim_stack + sizeof(interim_stack))
	 : "rax", "rbx", "rcx", "rdx", "rsi",
	   "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
	   "flags" );

    printf("Should now be being interpreted\n");
}
