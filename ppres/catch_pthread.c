#include "valgrind.h"
#include "ppres_client.h"
#include "audit.h"

int
audit_this_function(const char *name)
{
	if (!strcmp(name, "pthread_mutex_lock") ||
	    !strcmp(name, "pthread_mutex_unlock") ||
	    !strcmp(name, "pthread_create"))
		return 1;
	else
		return 0;
}

struct trampoline {
	void *(*r)(void *);
	void *arg;
};

static void *
my_start_routine(void *tramp)
{
	struct trampoline *tr = tramp;
	void *(*f)(void *r);
	void *arg;
	unsigned rv;
	VALGRIND_DO_CLIENT_REQUEST(rv, 0,
				   VG_USERREQ_PPRES_CALLED_LIBRARY,
				   "pthread_create_child", 0, 0, 0, 0);
	f = tr->r;
	arg = tr->arg;
	free(tr);
	return f(arg);
}

static void
enter_monitor(void)
{
	unsigned rv;

	VALGRIND_DO_CLIENT_REQUEST(rv, 0,
				   VG_USERREQ_TOOL_BASE('E', 'A'),
				   0, 0, 0, 0, 0);
}

/* Need to be a bit careful when exiting monitor mode, because PPRES
   asserts that RCX and RDX are the same between record and replay,
   and they might be different due to e.g. the locking implementation
   having done something subtly different (the locks are themselves in
   monitor mode, so we PPRES won't try to do full replay on them). */
static void
exit_monitor(void)
{
	unsigned code = VG_USERREQ_TOOL_BASE('E', 'A') + 1;
	asm volatile ("rolq $3, %%rdi\n"
		      "rolq $13, %%rdi\n"
		      "rolq $61, %%rdi\n"
		      "rolq $51, %%rdi\n"
		      "xchgq %%rbx, %%rbx\n"
		      :
		      : "a" (&code),
			"c" (0),
			"d" (0)
		      : "memory", "cc");
}

int
pre_func_audit(const char *name, unsigned long *args, unsigned long *res,
	       unsigned long val)
{
	unsigned rv;

	VALGRIND_DO_CLIENT_REQUEST(rv, 0,
				   VG_USERREQ_PPRES_CALL_LIBRARY,
				   name, 0, 0, 0, 0);
	if (!strcmp(name, "pthread_create")) {
		int r;
		struct trampoline *trampoline;
		trampoline = malloc(sizeof(*trampoline));
		trampoline->r = args[2];
		trampoline->arg = args[3];
		exit_monitor();
		r = ((int (*)(void *, void *, void *(*)(void *), void *))val)((void *)args[0],
									      (void *)args[1],
									      my_start_routine,
									      trampoline);
		enter_monitor();
		if (r != 0)
			free(trampoline);
		*res = r;
		VALGRIND_DO_CLIENT_REQUEST(rv, 0,
					   VG_USERREQ_PPRES_CALLED_LIBRARY,
					   "pthread_create", 0, 0, 0, 0);
		return 1;
	} else {
		return 0;
	}
}

void
post_func_audit(const char *name, unsigned long *res)
{
	unsigned rv;
	VALGRIND_DO_CLIENT_REQUEST(rv, 0,
				   VG_USERREQ_PPRES_CALLED_LIBRARY,
				   name, 0, 0, 0, 0);
}
