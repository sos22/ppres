#include <pthread.h>

unsigned global;
pthread_mutex_t mux;

#define NR_LOOPS 1000

static void
thread(void)
{
  unsigned x;
  for (x = 0; x < NR_LOOPS; x++) {
    pthread_mutex_lock(&mux);
    global++;
    pthread_mutex_unlock(&mux);
  }
}

int
main()
{
  pthread_t pthr;
  unsigned x;

  pthread_mutex_init(&mux, NULL);
  pthread_create(&pthr, NULL, thread, NULL);
  for (x = 0; x < NR_LOOPS; x++) {
    pthread_mutex_lock(&mux);
    global *= 3;
    pthread_mutex_unlock(&mux);
  }
  return global / 5;
}
