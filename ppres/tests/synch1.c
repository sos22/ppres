#include <pthread.h>

pthread_mutex_t mux;

static void
thread(void)
{
  pthread_mutex_lock(&mux);
  pthread_mutex_unlock(&mux);
}

int
main()
{
  pthread_t pthr;

  pthread_mutex_init(&mux, NULL);
  pthread_mutex_lock(&mux);
  pthread_create(&pthr, NULL, thread, NULL);
  sleep(1);
  pthread_mutex_unlock(&mux);
  return 0;
}
