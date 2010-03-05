extern unsigned char critical_section_prologue[];
extern unsigned char critical_section_epilogue[];

struct binpatch_label {
	enum {
		bpl_offset,
		bpl_absolute
	} type;
	unsigned long data;
};

struct binpatch_fixup {
	unsigned offset;
	unsigned addend;
	unsigned size;
	unsigned is_relative;
	struct binpatch_label label;
};

struct binpatch {
	unsigned long rip;
	void *pattern;
	unsigned pattern_size;
	struct binpatch_fixup *fixups;
	unsigned nr_fixups;
	void *patch;
	unsigned long pad0;
	unsigned long pad1;
};

#include "binpatch.c"

#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/ptrace.h>
#include <sys/mman.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <err.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

extern struct binpatch first_fixup[] __attribute__((visibility ("hidden")));
extern struct binpatch last_fixup[] __attribute__((visibility ("hidden")));

static void
sigtrap_sigaction(int sig, siginfo_t *info, void *_ctxt)
{
	ucontext_t *ctxt = _ctxt;
	unsigned long rip = ctxt->uc_mcontext.gregs[REG_RIP];
	struct binpatch *ff;

	ctxt->__fpregs_mem.mxcsr &= 0xffff;
	for (ff = first_fixup; ff < last_fixup; ff++) {
		if (rip == ff->rip) {
			ctxt->uc_mcontext.gregs[REG_RIP] = (unsigned long)ff->patch;
			setcontext(ctxt);
			errx(1, "back from setcontext?");
		}
	}
	errx(1, "sigtrap at bad address %lx", rip);
}

static pthread_mutex_t thelock;

static void
apply_fixup(const struct binpatch_fixup *fixup,
	    void *buffer)
{
	unsigned long value;

	switch (fixup->label.type) {
	case bpl_offset:
		value = (unsigned long)buffer + fixup->label.data;
		break;
	case bpl_absolute:
		value = fixup->label.data;
		break;
	}
	if (fixup->is_relative)
		value -= (unsigned long)buffer + fixup->offset;
	value -= fixup->addend;
	memcpy(buffer + fixup->offset, &value, fixup->size);
}

static void *
alloc_page(void)
{
	void *res;
	res = mmap(NULL, PAGE_SIZE, PROT_READ|PROT_WRITE|PROT_EXEC,
		   MAP_PRIVATE|MAP_32BIT|MAP_ANONYMOUS|MAP_EXECUTABLE,
		   -1, 0);
	if (res == MAP_FAILED)
		err(1, "mmap()");
	return res;
}

static void
mk_patch(struct binpatch *bp)
{
	void *patch;
	unsigned x;

	patch = alloc_page();
	memcpy(patch, bp->pattern, bp->pattern_size);
	for (x = 0; x < bp->nr_fixups; x++)
		apply_fixup(&bp->fixups[x], patch);
	bp->patch = patch;
}

/* Turn on all the fixups. */
static void
activate_fixups(void)
{
	struct sigaction sigact;
	struct binpatch *ff;
	unsigned dr_nr;
	pid_t child;

	pthread_mutex_init(&thelock, NULL);

	for (ff = first_fixup; ff < last_fixup; ff++)
		mk_patch(ff);

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
		int status;

		parent = getppid();
		dr_nr = 0;
		d7 = 0;
		if (ptrace(PTRACE_ATTACH, parent, 0, 0) < 0)
			err(1, "ptrace attach");
		if (waitpid(parent, &status, 0) < 0)
			err(1, "waiting for parent to stop");
		printf("first fixup %p, last %p\n", first_fixup, last_fixup);
		for (ff = first_fixup; ff < last_fixup; ff++) {
			printf("Add fixup %d %lx\n", dr_nr, ff->rip);
			if (ptrace(PTRACE_POKEUSER,
				   parent,
				   offsetof(struct user, u_debugreg[dr_nr]),
				   ff->rip) < 0)
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

void do_lock_c(void) __attribute__((visibility ("hidden")));
void do_unlock_c(void) __attribute__((visibility ("hidden")));

void
do_lock_c(void)
{
	pthread_mutex_lock(&thelock);
}

void
do_unlock_c(void)
{
	pthread_mutex_unlock(&thelock);
}
