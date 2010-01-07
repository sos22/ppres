#include <pthread.h>

static void
thread(void)
{
}

int
main()
{
  pthread_t pthr;

  pthread_create(&pthr, NULL, thread, NULL);
  return 0;
}
