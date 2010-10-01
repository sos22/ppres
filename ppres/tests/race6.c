/* Simple use-after-free race */
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 10000
static void *buffer;

static pthread_barrier_t barrier;

static void *
thread_start(void *ignore)
{
	pthread_barrier_wait(&barrier);
	free(buffer);
	buffer = NULL;
	return NULL;
}

int
main()
{
	pthread_t thread;

	buffer = malloc(BUFFER_SIZE);
	pthread_barrier_init(&barrier, NULL, 2);
	pthread_create(&thread, NULL, thread_start, NULL);

	pthread_barrier_wait(&barrier);
	if (buffer)
		memset(buffer, 0x73, BUFFER_SIZE);

	return 0;
}
