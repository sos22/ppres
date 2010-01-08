#include <pthread.h>

unsigned global;

static void
thread(void)
{
  unsigned x;
  for (x = 0; x < 1000000; x++)
    global++;
}

int
main()
{
  pthread_t pthr;
  unsigned x;

  pthread_create(&pthr, NULL, thread, NULL);
  for (x = 0; x < 1000000; x++)
    global++;
  return 0;
}
