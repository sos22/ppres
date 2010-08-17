#define _GNU_SOURCE
#include <sys/types.h>
#include <asm/prctl.h>
#include <asm/unistd.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/user.h>
#include <dirent.h>
#include <errno.h>
#include <sched.h>
#include <setjmp.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <linux/futex.h>

#include <libvex.h>
#include <libvex_guest_amd64.h>
#include <libvex_trc_values.h>
#include <pub_tool_basics.h>
#include <pub_tool_libcbase.h>
#include <pub_tool_libcassert.h>
#include <pub_tool_vki.h>
#include <pub_tool_libcfile.h>
#include <pub_tool_libcprint.h>
#include <pub_tool_libcproc.h>
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

void setup_file_descriptors(void);
Addr ML_(allocstack)(ThreadId tid);
extern UInt VG_(dispatch_ctr);
extern VgSchedReturnCode (*VG_(tool_provided_scheduler))(ThreadId);

static unsigned char interim_stack[16384];
static int memory_snapshot_completed;

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

static int
my_sleep(int seconds)
{
    struct timespec ts;
    long res;

    ts.tv_sec = seconds;
    ts.tv_nsec = 0;
    while (ts.tv_sec || ts.tv_nsec) {
	asm volatile ("syscall\n"
		      : "=a" (res)
		      : "0" (__NR_nanosleep),
			"D" (&ts),
			"S" (&ts)
		      : "rcx", "r11", "memory");
	if (res != EINTR)
	    return res;
    }
    return 0;
}

static int
my_futex(int *uaddr, int op, int val, const struct timespec *timeout,
	 int *uaddr2, int val3)
{
    long res;
    long ign;
    register unsigned long r8 asm("r8") = (unsigned long)uaddr2;
    register unsigned long r9 asm("r9") = val3;
    asm volatile ("syscall\n"
	 : "=a" (res), "=c" (ign)
	 : "0" (__NR_futex),
	   "D" (uaddr),
	   "S" (op),
	   "d" (val),
	   "1" (timeout),
	   "r" (r8),
	   "r" (r9)
	 : "r11", "memory");

    return res;
}

static int
my_ptrace(enum __ptrace_request request,
	  pid_t pid,
	  unsigned long addr,
	  unsigned long data)
{
    long res;
    long ign;
    asm volatile ("syscall\n"
		  : "=a" (res), "=c" (ign)
		  : "0" (__NR_ptrace),
		    "D" (request),
		    "S" (pid),
		    "d" (addr),
		    "1" (data)
		  : "r11", "memory");
    return res;
}

static unsigned long
get_fsbase()
{
    unsigned long buf;
    unsigned long ign;

    asm ("syscall\n"
	 : "=a" (ign)
	 : "0" (__NR_arch_prctl),
	   "D" (ARCH_GET_FS),
	   "S" (&buf)
	 : "memory", "rcx", "r11");
    return buf;
}

static void my_exit(int code)
{
    asm volatile ("syscall\n"
		  :
		  : "a" (__NR_exit),
		    "D" (code)
	);
}

static pid_t my_fork(void)
{
    long res;
    asm volatile ("syscall\n"
		  : "=a" (res)
		  : "0" (__NR_fork)
		  : "memory", "rcx", "r11");
    return res;
}

static void
my_err(int code, const char *fmt, ...)
{
    va_list args;
    VG_(printf)("Dying: ");
    va_start(args, fmt);
    VG_(vprintf)(fmt, args);
    my_exit(code);
}

static void
my_warn(const char *fmt, ...)
{
    va_list args;
    VG_(printf)("WARNING: ");
    va_start(args, fmt);
    VG_(vprintf)(fmt, args);
    va_end(args);
}

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

static VgSchedReturnCode
my_scheduler(ThreadId tid)
{
    ThreadState *volatile tas = VG_(get_ThreadState)(tid);

    block_signals();

    VG_(dispatch_ctr) = 10000;
    while (!VG_(is_exiting)(tid)) {
	int r;

	r = VG_(run_innerloop)(&tas->arch, 0);
	switch (r) {
	case VEX_TRC_JMP_SYS_SYSCALL: {
	    Bool jumped =  __builtin_setjmp(tas->sched_jmpbuf);
	    if (!jumped) {
		tas->sched_jmpbuf_valid = True;
		if (tas->arch.vex.guest_RAX == __NR_clone)
		    VG_(printf)("client clone syscall, rsp %llx\n",
				tas->arch.vex.guest_RSP);
		VG_(client_syscall)(tid, r);
	    }
	    tas->sched_jmpbuf_valid = False;
	    if (jumped) {
		block_signals();
		VG_(poll_signals)(tid);
	    }
	    break;
	}

	case VEX_TRC_JMP_YIELD:
	case VG_TRC_INNER_COUNTERZERO:
	    maybe_yield();
	    VG_(poll_signals)(tid);
	    VG_(dispatch_ctr) = 10000;
	    break;

	default:
	    VG_(printf)("Unknown VEX trace return %d\n", r);
	    VG_(tool_panic)((Char *)"dead");
	}
    }

    return tas->exitreason;
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
    VgSchedReturnCode res;

    tid = VG_(alloc_ThreadState)();

    if (tid == 1) {
	VG_(sigstartup_actions)();
	block_signals();
    }

    start_thread(tid);

    tas = &VG_(threads)[tid];
    gas = &tas->arch.vex;

    gas->guest_RSP = initial_rsp;
    gas->guest_RIP = initial_rip;
    gas->guest_FS_ZERO = get_fsbase();

    asm ("stmxcsr %0\n"
	 : "=m" (mxcsr));

    gas->guest_SSEROUND = (mxcsr >> 13) & 3;

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

    snapshot_memory();

    memory_snapshot_completed = 1;
    /* sys_futex() semantics don't include a wake-everyone operation,
       so just iterate a few times waking up 100 threads each time.
       This is really paranoia: you only need multiple iterations if
       you have >100 threads, which sounds unlikely. */
    while (my_futex(&memory_snapshot_completed, FUTEX_WAKE, 100, NULL,
		    NULL, 0))
	;

    tas->os_state.lwpid = VG_(gettid)();
    tas->os_state.threadgroup = VG_(getpid)();
    res = my_scheduler(tid);

    if (VG_(count_living_threads)() == 1) {
	( * VG_(address_of_m_main_shutdown_actions_NORETURN) ) (tid, res);
    } else {
	VG_(exit_thread)(tid);
	asm volatile (
	    "movl	%1, %0\n"	/* set tst->status = VgTs_Empty */
	    "syscall\n"		/* exit(tst->os_state.exitcode) */
	    : "=m" (tas->status)
	    : "n" (VgTs_Empty), "rax" (__NR_exit), "rdi" (tas->os_state.exitcode));
    }
}

static void
new_thread_capture(ThreadId tid)
{
    ThreadState *tas = &VG_(threads)[tid];
    VgSchedReturnCode res;

    VG_(printf)("Capturing %d\n", tid);

    /* Wait for the big memory snapshot to be completed */
    while (!memory_snapshot_completed)
	my_futex(&memory_snapshot_completed, FUTEX_WAIT, 0, NULL,
		 NULL, 0);

    start_thread(tid);

    /* Most of the capture work is already done. */
    tas->os_state.lwpid = VG_(gettid)();
    tas->os_state.threadgroup = VG_(getpid)();

    /* Start interpreting. */
    res = my_scheduler(tid);

    VG_(printf)("Thread %d going away; VG state %d, OS status %ld\n", tid, res,
		tas->os_state.exitcode);

    if (VG_(count_living_threads)() == 1) {
	( * VG_(address_of_m_main_shutdown_actions_NORETURN) ) (tid, res);
    } else {
	VG_(exit_thread)(tid);
	asm volatile (
	    "movl	%1, %0\n"	/* set tst->status = VgTs_Empty */
	    "syscall\n"		/* exit(tst->os_state.exitcode) */
	    : "=m" (tas->status)
	    : "n" (VgTs_Empty), "rax" (__NR_exit), "rdi" (tas->os_state.exitcode));
    }

}

static int
my_waitpid(pid_t pid)
{
    int status;
    unsigned long res;
    unsigned long ign;

    asm ("syscall\n"
	 : "=a" (res), "=c" (ign)
	 : "0" (__NR_wait4),
	   "D" (pid),
	   "S" (&status),
	   "d" (0),
	   "1" (0)
	 : "r11", "memory");

    return res;
}

static void
copy_via_ptrace(const void *src, size_t size, pid_t pid,
		unsigned long remote_address)
{
    unsigned x;
    for (x = 0; x < size; x += 8) {
	if (my_ptrace(PTRACE_POKEDATA, pid, remote_address + x,
		      *(unsigned long *)(src + x)) < 0)
	    my_err(1, "synchronising registers into %d, progress %d/%zd", pid,
		   x, size);
    }
}

static void
slurp_via_ptrace(pid_t other, ThreadId tid, unsigned long stack)
{
    ThreadState *tas;
    VexGuestArchState *gas;
    struct user_regs_struct regs;
    struct user_fpregs_struct fpregs;
    unsigned x;
    int r;

    tas = &VG_(threads)[tid];
    gas = &tas->arch.vex;

    if (my_ptrace(PTRACE_ATTACH, other, 0, 0) < 0)
	my_err(1, "attaching to %d", other);

    /* XXX: There's a race somewhere.  Make it go away. */
    my_sleep(5);

    r = my_waitpid(other);

    /* Slurp out its brains XXX can we share any of this with the main
     * thread conversion bits? */
    if (my_ptrace(PTRACE_GETREGS, other, 0, (unsigned long)&regs) < 0)
	my_err(1, "getting registers");

    /* Initialise the guest state. */
    memset(gas, 0, sizeof(*gas));
#define DO_REG(vg_name, linux_name)		\
    gas->guest_ ## vg_name = regs. linux_name
    DO_REG(RAX, rax);
    DO_REG(RCX, rcx);
    DO_REG(RDX, rdx);
    DO_REG(RBX, rbx);
    DO_REG(RSP, rsp);
    DO_REG(RBP, rbp);
    DO_REG(RSI, rsi);
    DO_REG(RDI, rdi);
    DO_REG(R8, r8);
    DO_REG(R9, r9);
    DO_REG(R10, r10);
    DO_REG(R11, r11);
    DO_REG(R12, r12);
    DO_REG(R13, r13);
    DO_REG(R14, r14);
    DO_REG(R15, r15);
    gas->guest_CC_OP = AMD64G_CC_OP_COPY;
    DO_REG(CC_DEP1, eflags);
    if (regs.eflags & (1 << 10))
	gas->guest_DFLAG = -1;
    else
	gas->guest_DFLAG = 1;
    DO_REG(RIP, rip);
    gas->guest_IDFLAG = !!(regs.eflags & (1 << 21));
    DO_REG(FS_ZERO, fs_base);
#undef DO_REG

    if (my_ptrace(PTRACE_GETFPREGS, other, 0, (unsigned long)&fpregs) < 0)
	my_err(1, "getting FP registers");
    gas->guest_SSEROUND = (fpregs.mxcsr >> 13) & 3;
    gas->guest_FTOP = (fpregs.swd >> 10) & 7;

    /* transfer FP registers.  Annoyingly, Valgrind stores them as 64
     * bit doubles (which is wrong, but whatever), while Linux uses 80
     * bit extended doubles padded to 128 bits.  This means we need to
     * do an annoying conversion step. */
    /* Note that we truncate rather than rounding, which isn't
     * actually correct but seems to mostly work. */
    for (x = 0; x < 8; x++) {
	unsigned long frac = (fpregs.st_space[x * 2] & ~(1ul << 63)) >> 11;
	unsigned long exponent = fpregs.st_space[x * 2 + 1] & 0x7ff;
	unsigned long sign = (fpregs.st_space[x * 2 + 1] >> 15) & 1;
	gas->guest_FPREG[x] = (sign << 63) |
	    (exponent << 52) |
	    frac;
    }

    for (x = 0; x < 8; x++)
	gas->guest_FPTAG[x] = (fpregs.ftw >> (x * 2)) & 3;
    gas->guest_FPROUND = (fpregs.cwd >> 9) & 3;
    gas->guest_FC3210 = ((fpregs.swd >> 8) & 7) | ((fpregs.swd >> 11) & 8);
    memcpy(&gas->guest_XMM0, fpregs.xmm_space, 256);

    copy_via_ptrace(gas, sizeof(*gas), other, (unsigned long)gas);

    /* Okay, the thread is now properly captured.  Allocate a new
       stack for it and then cajole it onto the trampoline. */
    regs.rsp = stack;
    regs.rdi = tid;
    regs.rip = (unsigned long)new_thread_capture + 2;
    regs.r13 = 0x1122334455667788ul;
    if (my_ptrace(PTRACE_SETREGS, other, 0, (unsigned long)&regs) < 0)
	my_err(1, "imposing will on %d", other);

    if (my_ptrace(PTRACE_GETREGS, other, 0, (unsigned long)&regs) < 0)
	my_err(1, "regetting registers of %d", other);

    VG_(printf)("detaching, rip %lx, stack %lx\n",
		regs.rip, regs.rsp);

    if (my_ptrace(PTRACE_DETACH, other, 0, 0) < 0)
	my_err(1, "detaching %d", other);

    my_exit(0);
}

static void
attach_thread(pid_t other)
{
    ThreadId tid;
    unsigned long new_stack;
    unsigned long worker;
    int r;

    tid = VG_(alloc_ThreadState)();

    if (tid == 1) {
	VG_(printf)("Spin up sighandlers\n");
	VG_(sigstartup_actions)();
	/* sigstartup blocks sync signals as well, so unblock them
	   here. */
	/* Yes, block_signals() really is the right function to use to
	   unblock sync signals. */
	block_signals();
    }

    new_stack = ML_(allocstack)(tid);

    worker = my_fork();
    if (worker == 0)
	slurp_via_ptrace(other, tid, new_stack);

    r = my_waitpid(worker);
}

typedef struct {
    int fd;
    char buf[8192];
    int next_offset;
    int buffer_start; /* Offset of buf[0] in file */
    int buffer_end; /* Last offset in file which is present in buf */
} MY_DIR;

static MY_DIR *
my_opendir(const char *path)
{
    SysRes sr;
    int fd;
    MY_DIR *res;

    sr = VG_(open)((const Char *)path, VKI_O_RDONLY, 0);
    if (sr_isError(sr))
	return NULL;
    fd = sr_Res(sr);

    res = VG_(malloc)((HChar *)"MY_DIR", sizeof(*res));
    memset(res, 0, sizeof(*res));
    res->fd = fd;

    return res;
}

static void
replenish_buffer(MY_DIR *d)
{
    Int r;

    VG_(memmove)(d->buf,
		 d->buf + d->next_offset - d->buffer_start,
		 d->buffer_end - d->next_offset);
    d->buffer_start = d->next_offset;
    r = VG_(getdents)(d->fd,
		      (void *)d->buf + d->buffer_end - d->buffer_start,
		      sizeof(d->buf) - (d->buffer_end - d->buffer_start));
    d->buffer_end += r;
}

struct linux_dirent {
    long d_ino;
    long d_off;
    unsigned short d_reclen;
    char d_name[0];
};

static char *
my_readdir(MY_DIR *d)
{
    struct linux_dirent *raw_de;

    VG_(printf)("Buffer %d:%d, next offset %d\n",
		d->buffer_start, d->buffer_end,
		d->next_offset);
    if (d->next_offset + sizeof(*raw_de) > d->buffer_end) {
	VG_(printf)("Replenish\n");
	replenish_buffer(d);
	if (d->buffer_start == d->buffer_end) {
	    /* EOF */
	    return NULL;
	}
	if (d->next_offset + sizeof(*raw_de) > d->buffer_end)
	    my_err(1, "corrupted directory");
    }
    VG_(printf)("Got header at %d, buffer %d:%d\n",
		d->next_offset, d->buffer_start, d->buffer_end);
    raw_de = (struct linux_dirent *)(d->buf + d->next_offset - d->buffer_start);
    if (d->next_offset + raw_de->d_reclen > d->buffer_end) {
	replenish_buffer(d);
	raw_de = (struct linux_dirent *)(d->buf + d->next_offset - d->buffer_start);
	if (d->next_offset + raw_de->d_reclen > d->buffer_end)
	    my_err(1, "corrupted directory 2: %d + %d > %d",
		   d->next_offset, raw_de->d_reclen, d->buffer_end);
    }

    VG_(printf)("Got de name %s next offset %ld reclen %d\n",
		raw_de->d_name, raw_de->d_off,
		raw_de->d_reclen);
    d->next_offset += raw_de->d_reclen;
    return raw_de->d_name;
}

static void
my_closedir(MY_DIR *d)
{
    VG_(close)(d->fd);
    VG_(free)(d);
}

void
start_interpreting(unsigned long initial_rsp, unsigned long initial_rip)
{
    pid_t self = VG_(getpid)();
    pid_t other;
    char path[4096];
    MY_DIR *d;
    char *de_name;

    initialise_valgrind(initial_rsp);

    VG_(sprintf)((Char *)path, "/proc/%d/task", self);
    d = my_opendir(path);
    if (!d) {
	/* Give up */
	my_warn("opening %s", path);
	return;
    }
    while (1) {
	de_name = my_readdir(d);
	if (!de_name)
	    break;
	if (!strcmp(de_name, ".") ||
	    !strcmp(de_name, ".."))
	    continue;
	other = VG_(strtoll10)((Char *)de_name, NULL);
	if (other == self)
	    continue;

	VG_(printf)("Attach to %d\n", other);
	attach_thread(other);
    }
    my_closedir(d);

    my_sleep(7);

    run_thread(initial_rsp, initial_rip);

    VG_(printf)("Thread exitted?\n");
}

void
_init()
{
    unsigned long ign;
    unsigned x;

    for (x = 0; x < VG_N_THREADS; x++)
	VG_(threads)[x].tid = x;

    VG_(tool_provided_scheduler) = my_scheduler;

    asm volatile ("pushq %%rbp\n"
		  "lea 1f(%%rip), %%rsi\n"
		  "xchg %%rsp, %%rdi\n"
		  "call start_interpreting@PLT\n"
		  
		  "1:\n" /* We never actually run this, but it's the first
			    thing which gets interpreted.  Everything register
			    except rip, rsp, and the floating point state is
			    clobbered when we get here. */
		  "popq %%rbp\n" /* Can't asm clobber rbp, so save it
				  * ourselves. */
		  : "=D" (ign)
		  : "0" (interim_stack + sizeof(interim_stack))
		  : "rax", "rbx", "rcx", "rdx", "rsi",
		    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
		    "flags", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5",
		    "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11",
		    "xmm12", "xmm13", "xmm14", "xmm15", "memory" );
}
