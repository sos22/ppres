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
		VALGRIND_DO_CLIENT_REQUEST(rv, 0,
					   VG_USERREQ_TOOL_BASE('E', 'A') + 1,
					   0, 0, 0, 0, 0);
		r = ((int (*)(void *, void *, void *(*)(void *), void *))val)((void *)args[0],
									      (void *)args[1],
									      my_start_routine,
									      trampoline);
		VALGRIND_DO_CLIENT_REQUEST(rv, 0,
					   VG_USERREQ_TOOL_BASE('E', 'A'),
					   0, 0, 0, 0, 0);
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
