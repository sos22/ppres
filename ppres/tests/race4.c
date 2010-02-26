/* Bug kernel of glibc bug 2644.  The original code looked like this:

_Unwind_Reason_Code
_Unwind_ForcedUnwind (struct _Unwind_Exception *exc, _Unwind_Stop_Fn stop,
		      void *stop_argument)
{
   if (__builtin_expect (libgcc_s_forcedunwind == NULL, 0))
      pthread_cancel_init ();
   return libgcc_s_forcedunwind (exc, stop, stop_argument);
}

void
pthread_cancel_init (void)
{
      void *resume, *personality, *forcedunwind, *getcfa;
      void *handle;

      if (__builtin_expect (libgcc_s_getcfa != NULL, 1))
	return;

      handle = __libc_dlopen ("libgcc_s.so.1");

      if (handle == NULL
	  || (resume = __libc_dlsym (handle, "_Unwind_Resume")) == NULL
	  || (personality = __libc_dlsym (handle, "__gcc_personality_v0")) == NULL
	  || (forcedunwind = __libc_dlsym (handle, "_Unwind_ForcedUnwind"))
	     == NULL
	  || (getcfa = __libc_dlsym (handle, "_Unwind_GetCFA")) == NULL
	  || ARCH_CANCEL_INIT (handle)
	  )
	__libc_fatal ("libgcc_s.so.1 must be installed for pthread_cancel to work\n");

      libgcc_s_resume = resume;
      libgcc_s_personality = personality;
      libgcc_s_forcedunwind = forcedunwind;
      libgcc_s_getcfa = getcfa;
}

  and pthread_cancel_init() got inline into _Unwind_ForcedUnwind, which meant that
  libgcc_s_forcedunwind() could be cached between the two referenced.  Some other
  thread got in between the test of libgcc_s_forcedunwind in _Unwind_ForcedUnwind
  and the test of libgcc_s_getcfs() in pthread_cancel_init() and initialised both
  pointers, so the inlined pthread_cancel_init() didn't do anything and we
  ended up calling NULL.

  We reduce the bug to this:

void
unwind_forcedunwind(void)
{
     l = gcc_s_forcedunwind;
     if (!l) {
        if (!done_init) {
           gcc_s_forcedunwind = gcc_s_forcedunwind_impl;
           l = gcc_s_forcedunwind;
           done_init = 1;
        }
     }
     l();
}

*/
/* Keep emacs happy: ' */
#include <pthread.h>

static void (*gcc_s_forcedunwind)(void);
static int done_init;

static void
gcc_s_forcedunwind_impl(void)
{
}

void
unwind_forcedunwind(void)
{
	void (*l)(void);
	l = gcc_s_forcedunwind;
	if (!l) {
		if (!done_init) {
			gcc_s_forcedunwind = gcc_s_forcedunwind_impl;
			l = gcc_s_forcedunwind;
			done_init = 1;
		}
	}
	l();
}

static pthread_barrier_t barrier;

static void *
thread_start(void *ignore)
{
	while (1) {
		pthread_barrier_wait(&barrier);
		unwind_forcedunwind();
		pthread_barrier_wait(&barrier);
	}
}

int
main()
{
	pthread_t thread;
	unsigned cntr;

	pthread_barrier_init(&barrier, NULL, 2);
	pthread_create(&thread, NULL, thread_start, NULL);

	cntr = 0;
	while (1) {
		cntr++;
		done_init = 0;
		gcc_s_forcedunwind = NULL;
		pthread_barrier_wait(&barrier);
		unwind_forcedunwind();
		pthread_barrier_wait(&barrier);
	}
}
