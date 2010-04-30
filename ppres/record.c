#define _LARGEFILE64_SOURCE
#include <asm/ioctl.h>
#include <asm/ioctls.h>
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

#include "../coregrind/pub_core_threadstate.h"

#include "ppres.h"

extern ULong (*tool_provided_rdtsc)(void);

#define DEBUG(fmt, args...) //VG_(printf)(fmt, ## args)

#define RECORD_BLOCK_SIZE 16384
#define MAX_RECORD_SIZE 4096
#define INDEX_PERIOD 1000000

struct record_emitter {
	int fd;
	int index_fd;
	void *current_block;
	unsigned current_block_used;
	unsigned long nr_records;
	unsigned long offset_in_file;
};

static struct record_emitter
logfile;

static void
open_logfile(struct record_emitter *res,
	     const signed char *fname)
{
	SysRes open_res;
	Char buf[4096];

	VG_(sprintf)(buf, "%s.idx", fname);
	open_res = VG_(open)(fname, O_WRONLY|O_CREAT|O_TRUNC|O_LARGEFILE,
			     0700);
	res->fd = sr_Res(open_res);
	res->index_fd = sr_Res(VG_(open)(buf, O_WRONLY|O_CREAT|O_TRUNC|O_LARGEFILE,
					 0700));
	res->current_block = VG_(malloc)("logbuffer",
					 RECORD_BLOCK_SIZE);
	res->current_block_used = 0;
	res->nr_records = 0;
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

static void
write_index_record(int fd, unsigned long nr_records, unsigned long offset_in_file)
{
	struct index_record ir;
	ir.record_nr = nr_records;
	ir.offset_in_file = offset_in_file;
	VG_(write)(fd, &ir, sizeof(ir));
}

static void *
emit_record(struct record_emitter *re,
	    unsigned record_class,
	    unsigned record_size)
{
	struct record_header *hdr;

	if (!(re->nr_records % INDEX_PERIOD))
		write_index_record(re->index_fd, re->nr_records, re->offset_in_file);
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
	re->offset_in_file += record_size;

	re->nr_records++;
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
record_instr(Word addr, Word reg0, Word reg1, Word reg2, Word reg3, Word reg4)
{
	struct footstep_record *fr;
	if (client_in_monitor())
		return;
	fr = emit_record(&logfile, RECORD_footstep, sizeof(*fr));
	fr->rip = addr;
	fr->FOOTSTEP_REG_0_NAME = reg0;
	fr->FOOTSTEP_REG_1_NAME = reg1;
	fr->FOOTSTEP_REG_2_NAME = reg2;
	fr->FOOTSTEP_REG_3_NAME = reg3;
	fr->FOOTSTEP_REG_4_NAME = reg4;
}

static void
record_load(const void *ptr, unsigned size, void *base, unsigned long rsp,
	    unsigned long rip)
{
	struct mem_read_record *mrr;
	VG_(memcpy)(base, ptr, size);
	if (!IS_STACK(ptr, rsp)) {
		mrr = emit_record(&logfile, RECORD_mem_read, sizeof(*mrr) + size);
		mrr->ptr = (Word)ptr;
		VG_(memcpy)(mrr + 1, base, size);
	}
}

static void
record_store(void *ptr, unsigned size, const void *base, unsigned long rsp,
	     unsigned long rip)
{
	struct mem_write_record *mrr;
	VG_(memcpy)(ptr, base, size);
	if (!IS_STACK(ptr, rsp)) {
		mrr = emit_record(&logfile, RECORD_mem_write, sizeof(*mrr) + size);
		mrr->ptr = (Word)ptr;
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

#define __statfs_word long
struct kernel_statfs {
        __statfs_word f_type;
        __statfs_word f_bsize;
        __statfs_word f_blocks;
        __statfs_word f_bfree;
        __statfs_word f_bavail;
        __statfs_word f_files;
        __statfs_word f_ffree;
        __kernel_fsid_t f_fsid;
        __statfs_word f_namelen;
        __statfs_word f_frsize;
        __statfs_word f_spare[5];
};

static void
emit_triv_syscall(UInt nr, SysRes res, UWord *args)
{
	struct syscall_record *sr;

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
	if (signo == VKI_SIGBUS || signo == VKI_SIGSEGV) {
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
		switch (syscall_args[1] & FUTEX_CMD_MASK) {
		case FUTEX_WAIT:
		case FUTEX_WAIT_BITSET: {
			int expected;
			int observed;
			expected = syscall_args[2];
			record_load((int *)syscall_args[0], 4, &observed, 0, 0);
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

typedef unsigned char   cc_t;
typedef unsigned int    tcflag_t;
#define NCCS 19
struct termios {
        tcflag_t c_iflag;               /* input mode flags */
        tcflag_t c_oflag;               /* output mode flags */
        tcflag_t c_cflag;               /* control mode flags */
        tcflag_t c_lflag;               /* local mode flags */
        cc_t c_line;                    /* line discipline */
        cc_t c_cc[NCCS];                /* control characters */
};
struct winsize {
        unsigned short ws_row;
        unsigned short ws_col;
        unsigned short ws_xpixel;
        unsigned short ws_ypixel;
};

static void
handle_ioctl(UWord *syscall_args, UInt nr_args, SysRes res)
{
	UWord code = syscall_args[1];
	const char *dir_strings[4] = { "_IOC_NONE",
				       "_IOC_WRITE",
				       "_IOC_READ",
				       "_IOC_<bad>" };
	switch (code) {
	case TCGETS:
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[2],
				       sizeof(struct termios));
		break;
	case TIOCGWINSZ:
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[2],
				       sizeof(struct winsize));
		break;
	default:
		VG_(printf)("don't know what to do with ioctl %lx (_IOC(%ld=%s,%ld=%c,%ld,%ld))\n",
			    code,
			    _IOC_DIR(code),
			    dir_strings[_IOC_DIR(code)],
			    _IOC_TYPE(code),
			    (unsigned char)_IOC_TYPE(code),
			    _IOC_NR(code),
			    _IOC_SIZE(code));
		VG_(exit)(1);
	}
}

static void
handle_fcntl(UWord *syscall_args, UInt nr_args, SysRes res)
{
	switch (syscall_args[1]) {
		/* Most fcntl commands have no memory arguments */
	case F_GETFD:
		break;
	default:
		VG_(printf)("Don't know how to handle fcntl %lx\n",
			    syscall_args[1]);
		VG_(exit)(1);
	}
}

static void
post_syscall(ThreadId tid, UInt syscall_nr, UWord *syscall_args, UInt nr_args,
	     SysRes res)
{
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

	case __NR_ioctl:
		handle_ioctl(syscall_args, nr_args, res);
		break;

	case __NR_fcntl:
		handle_fcntl(syscall_args, nr_args, res);
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

	case __NR_getdents:
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

	case __NR_statfs:
		if (!sr_isError(res))
			capture_memory((void *)syscall_args[1],
				       sizeof(struct kernel_statfs));
		break;

	case __NR_futex: {
		/* Often need to modify pre_syscall when you modify
		 * this. */
		switch (syscall_args[1] & FUTEX_CMD_MASK) {
		case FUTEX_WAKE:
			/* No special handling needed */
			break;
		case FUTEX_WAIT:
		case FUTEX_WAIT_BITSET:
			if (!sr_isError(res) ||
			    sr_Err(res) != EWOULDBLOCK)
				emit_record(&logfile, RECORD_thread_unblocked, 0);
			break;
		default:
			VG_(printf)("Don't understand futex operation %ld\n",
				    syscall_args[1] & FUTEX_CMD_MASK);
			VG_(tool_panic)((Char *)"Not implemented yet");
		}
		break;
	}

	default:
		VG_(printf)("don't know what to do with syscall %d\n", syscall_nr);
		VG_(exit)(1);
	}
}

static char *
parse_hex(char *start, unsigned long *outp)
{
	*outp = 0;
	while (1) {
		if (start[0] >= '0' && start[0] <= '9') {
			*outp *= 16;
			*outp += start[0] - '0';
			start++;
		} else if (start[0] >= 'a' && start[0] <= 'f') {
			*outp *= 16;
			*outp += start[0] - 'a' + 10;
			start++;
		} else if (start[0] >= 'A' && start[0] <= 'F') {
			*outp *= 16;
			*outp += start[0] - 'A' + 10;
			start++;
		} else
			return start;
	}
}

static char *
parse_map_flags(char *line, unsigned *prot, unsigned *flags)
{
	*flags = MAP_PRIVATE;
	*prot = 0;
	switch (line[0]) {
	case 'r':
		*prot |= PROT_READ;
		break;
	case '-':
		break;
	default:
		VG_(tool_panic)((Char *)"can't parse /proc/self/maps");
	}
	switch (line[1]) {
	case 'w':
		*prot |= PROT_WRITE;
		break;
	case '-':
		break;
	default:
		VG_(tool_panic)((Char *)"can't parse /proc/self/maps");
	}
	switch (line[2]) {
	case 'x':
		*prot |= PROT_EXEC;
		break;
	case '-':
		break;
	default:
		VG_(tool_panic)((Char *)"can't parse /proc/self/maps");
	}
	if (line[3] != 'p' && line[3] != 's')
		VG_(tool_panic)((Char *)"can't parse /proc/self/maps");
	return line + 4;
}

static char *
skip_char(char *l, char c)
{
	if (l[0] != c)
		VG_(tool_panic)((Char *)"can't parse /proc/self/maps");
	return l + 1;
}

static char *
skip_spaces(char *l)
{
	while (l[0] == ' ' || l[0] == '\t')
		l++;
	return l;
}

static void
process_proc_line(char *line, struct record_emitter *logfile)
{
	unsigned long start, end;
	unsigned long ign;
	unsigned prot, flags;
	char *path;
	struct allocate_memory_record *amr;

	line = parse_hex(line, &start);
	line = skip_char(line, '-');
	line = parse_hex(line, &end);
	line = skip_spaces(line);
	line = parse_map_flags(line, &prot, &flags);
	line = skip_spaces(line);
	line = parse_hex(line, &ign); /* offset */
	line = skip_spaces(line);
	line = parse_hex(line, &ign); /* major */
	line = skip_char(line, ':');
	line = parse_hex(line, &ign); /* minor */
	line = skip_spaces(line);
	line = parse_hex(line, &ign); /* inode */
	path = skip_spaces(line);

	/* This isn't really ideal, but I don't know any other way of
	 * doing it. */
	if (!VG_(strcmp)((Char *)path, (Char *)"[vsyscall]"))
		return;
	if (!VG_(strcmp)((Char *)path, (Char *)"[stack]"))
		flags |= MAP_GROWSDOWN | MAP_STACK;

	if (!(prot & PROT_READ)) {
		/* Grant ourselves read access to the memory so that
		 * we can dump it out */
		/* This is kind of a stupid thing for a program to do
		   on x86 (because no read implies no access at all),
		   but it is technically valid, and the contents of
		   the memory can make a difference if they mprotect()
		   it later. */
		my_mprotect((void *)start,
			    end - start,
			    PROT_READ);
	}
	amr = emit_record(logfile, RECORD_allocate_memory, sizeof(*amr));
	amr->start = start;
	amr->size = end - start;
	amr->prot = prot;
	amr->flags = flags;
	capture_memory((void *)start, end - start);
	if (!(prot & PROT_READ)) {
		/* Put the protections back to what they were
		 * again. */
		my_mprotect((void *)start,
			    end - start,
			    prot);
	}
}

extern Addr  VG_(brk_limit);

static void
dump_snapshot(void)
{
	int fd;
	SysRes sr;
	char buf[4097];
	unsigned buffer_avail;
	unsigned buffer_line_start;
	unsigned buffer_line_cursor;
	Int read_this_time;
	VexGuestAMD64State *regs;
	struct initial_brk_record *ibr;

	regs = emit_record(&logfile, RECORD_initial_registers, sizeof(*regs));
	*regs = VG_(threads)[1].arch.vex;

	ibr = emit_record(&logfile, RECORD_initial_brk, sizeof(*ibr));
	ibr->initial_brk = VG_(brk_limit);

	sr = VG_(open)((Char *)"/proc/self/maps", VKI_O_RDONLY, 0);
	if (sr_isError(sr)) {
		VG_(printf)("cannot open /proc/self/maps: %ld\n",
			    sr_Err(sr));
		VG_(exit)(1);
	}
	fd = sr_Res(sr);
	buffer_avail = 0;
	buffer_line_start = 0;
	while (1) {
		for (buffer_line_cursor = buffer_line_start;
		     buffer_line_cursor < buffer_avail &&
			     buf[buffer_line_cursor] != '\n';
		     buffer_line_cursor++)
			;
		if (buffer_line_cursor == buffer_avail) {
			VG_(memmove)(buf,
				     buf + buffer_line_start,
				     buffer_avail - buffer_line_start);
			buffer_avail -= buffer_line_start;
			buffer_line_cursor -= buffer_line_start;
			buffer_line_start = 0;
			read_this_time = VG_(read)(fd,
						   buf + buffer_avail,
						   sizeof(buf) - buffer_avail - 1);
			if (read_this_time == 0) {
				if (buffer_avail == 0) {
					break;
				} else {
					/* We've hit the end of the
					   file, but still need to
					   finish off the current
					   line. */
					buffer_line_cursor = buffer_avail;
				}
			} else if (read_this_time < 0) {
				VG_(printf)("Error reading from /proc/self/maps\n");
				VG_(exit)(1);
			} else {
				buffer_avail += read_this_time;
				continue;
			}
		}
		buf[buffer_line_cursor] = 0;
		process_proc_line(buf + buffer_line_start, &logfile);
		buffer_line_start = buffer_line_cursor + 1;
	}
	VG_(close)(fd);
}

static void
init(void)
{
	open_logfile(&logfile, (signed char *)"logfile1");
}

static void
fini(Int ignore)
{
	VG_(printf)("fini\n");
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
	} else if (VG_IS_TOOL_USERREQ('E', 'A', arg_block[0])) {
		if ((arg_block[0] & 0xffff) == 0) {
			client_entering_monitor(tid);
		} else {
			client_exiting_monitor(tid);
		}
	}
	return False;
}

static void
pre_deliver_signal(ThreadId tid, Int signal, Bool alt_stack,
		   UWord err, UWord virtaddr, UWord rip)
{
	struct signal_record *sr;

	sr = emit_record(&logfile, RECORD_signal, sizeof(*sr));
	sr->rip = rip;
	sr->signo = signal;
	sr->err = err;
	sr->virtaddr = virtaddr;
}

extern void (*VG_(tool_about_to_start))(void);

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
	VG_(track_pre_deliver_signal)(pre_deliver_signal);

	VG_(tool_about_to_start) = dump_snapshot;
}

VG_DETERMINE_INTERFACE_VERSION(pre_clo_init)
