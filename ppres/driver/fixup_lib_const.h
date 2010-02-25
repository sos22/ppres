/* The bits of a fixup library which are shared across all such
   libraries.  This isn't really a normal header file, and shouldn't
   be #include'd into anything which hasn't come out of the fixup
   generator. */
#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/ptrace.h>
#include <sys/mman.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <err.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

struct fixup_desc {
	unsigned offset;
	unsigned addend;
	unsigned long target;
	unsigned size;
	unsigned relative;
};

struct fixup_table_entry {
	unsigned long orig;
	char *pattern;
	unsigned pattern_size;
	struct fixup_desc *fixups;
	unsigned nr_fixups;
	void *patch;
	unsigned long pad0;
	unsigned long pad1;
};

#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))

/* Flag that buffer is a relocated version of addr, and needs fixups
   applied to it befroe it becomes useful. */
#define REGISTER_FIXUP(addr, pattern, fixups)				\
static const struct fixup_table_entry __fixup_ ## fixups __attribute__ ((section ("fixup_table"))) = {	        \
	addr,								\
	pattern,							\
        sizeof(pattern),							\
	fixups,								\
        ARRAY_SIZE(fixups),						\
}

extern struct fixup_table_entry first_fixup __attribute__((visibility ("hidden")));
extern struct fixup_table_entry last_fixup __attribute__((visibility ("hidden")));

static void
sigtrap_sigaction(int sig, siginfo_t *info, void *_ctxt)
{
	ucontext_t *ctxt = _ctxt;
	unsigned long rip = ctxt->uc_mcontext.gregs[REG_RIP];
	struct fixup_table_entry *ff;

	ctxt->__fpregs_mem.mxcsr &= 0xffff;
	for (ff = &first_fixup; ff <= &last_fixup; ff++) {
		if (rip == ff->orig) {
			ctxt->uc_mcontext.gregs[REG_RIP] = (unsigned long)ff->patch;
			setcontext(ctxt);
			errx(1, "back from setcontext?");
		}
	}
	errx(1, "sigtrap at bad address %lx", rip);
}

static void
build_fixup(struct fixup_table_entry *ff)
{
	void *n;
	unsigned x;

	printf("Build patch for fixup at %lx\n", ff->orig);
	n = mmap(NULL, PAGE_SIZE, PROT_READ|PROT_WRITE|PROT_EXEC,
		 MAP_PRIVATE|MAP_32BIT|MAP_ANONYMOUS|MAP_EXECUTABLE,
		 -1, 0);
	if (n == MAP_FAILED)
		err(1, "mmap()");
	memcpy(n, ff->pattern, ff->pattern_size);
	for (x = 0; x < ff->nr_fixups; x++) {
		if (ff->fixups[x].relative) {
			if (ff->fixups[x].size == 8) {
				*(unsigned long *)(n + ff->fixups[x].offset) =
					ff->fixups[x].target - ((unsigned long)n + ff->fixups[x].offset + ff->fixups[x].addend);
			} else if (ff->fixups[x].size == 4) {
				*(unsigned *)(n + ff->fixups[x].offset) =
					ff->fixups[x].target - ((unsigned long)n + ff->fixups[x].offset + ff->fixups[x].addend);
			}
		} else {
			if (ff->fixups[x].size == 8) {
				*(unsigned long *)(n + ff->fixups[x].offset) = ff->fixups[x].target;
			} else if (ff->fixups[x].size == 4) {
				*(unsigned *)(n + ff->fixups[x].offset) = ff->fixups[x].target;
			}
		}
	}
	ff->patch = n;
	printf("Fixup for %lx at %p\n", ff->orig, ff->patch);
}

/* Turn on all the fixups. */
static void
activate_fixups(void)
{
	struct sigaction sigact;
	struct fixup_table_entry *ff;
	unsigned dr_nr;
	pid_t child;

	for (ff = &first_fixup; ff < &last_fixup; ff++)
		build_fixup(ff);

	/* Install the signal handler */
	sigact.sa_sigaction = sigtrap_sigaction;
	sigemptyset(&sigact.sa_mask);
	sigact.sa_flags = SA_SIGINFO;
	if (sigaction(SIGTRAP, &sigact, NULL) < 0)
		err(1, "installing SIGTRAP handler");

	/* Now go through and set up debug registers.  Need to do this
	 * from a new process, for kernel implementation reasons. */
	child = fork();
	if (child == 0) {
		pid_t parent;
		unsigned long d7;

		parent = getppid();
		dr_nr = 0;
		d7 = 0;
		if (ptrace(PTRACE_ATTACH, parent, 0, 0) < 0)
			err(1, "ptrace attach");
		for (ff = &first_fixup; ff < &last_fixup; ff++) {
			printf("Add fixup %d %lx\n", dr_nr, ff->orig);
			if (ptrace(PTRACE_POKEUSER,
				   parent,
				   offsetof(struct user, u_debugreg[dr_nr]),
				   ff->orig) < 0)
				err(1, "ptrace %d", dr_nr);

			/* Enable the register.  They're in
			   instruction mode by default, which is what
			   we want, so just turning it on is
			   sufficient. */
			d7 |= 1 << (dr_nr * 2);

			dr_nr++;
		}
		if (ptrace(PTRACE_POKEUSER,
			   parent,
			   offsetof(struct user, u_debugreg[7]),
			   d7) < 0)
			err(1, "ptrace 7");
		if (ptrace(PTRACE_DETACH, parent, 0, 0) < 0)
			err(1, "ptrace attach");
		_exit(0);
	} else {
		int status;

		if (waitpid(child, &status, 0) < 0)
			err(1, "waitpid()");
		if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
			errx(1, "bad status from child: %x", status);
	}

	/* We should now be ready to go. */
}

static void (*init_ptr)(void) __attribute__((section(".init_array"), unused)) = activate_fixups;

extern unsigned char do_lock;
extern unsigned char do_unlock;

void do_lock_c(void) __attribute__((visibility ("hidden")));
void do_unlock_c(void) __attribute__((visibility ("hidden")));

void
do_lock_c(void)
{
}

void
do_unlock_c(void)
{
}
