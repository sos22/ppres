/* Slightly expanded version of race4.c */
#include <pthread.h>
#include <dlfcn.h>
#include <stdio.h>

static void (*gcc_s_forcedunwind)(void);
static int done_init;

void
unwind_forcedunwind(void)
{
	void (*l)(void);
	l = gcc_s_forcedunwind;
	if (!l) {
		if (!done_init) {
			void *handle;
			handle = dlopen("./race5_shared.so", RTLD_LAZY);
			l = dlsym(handle, "gcc_s_forcedunwind_impl");
			gcc_s_forcedunwind = l;
			done_init = 1;
		}
	}
	l();
}

static pthread_barrier_t barrier;
static unsigned cntr;

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
