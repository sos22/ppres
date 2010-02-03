#include <sys/types.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>

volatile unsigned global;

static void *
thread(void *ignore)
{
  unsigned r1;
  unsigned r2;
  while (1) {
    r1 = global;
    r2 = global;
    if (r1 == r2)
      getuid();
    else
      abort();
  }
}

int
main()
{
  pthread_t pthr;
  unsigned x;

  pthread_create(&pthr, NULL, thread, NULL);
  while (1) {
    global++;
    for (x = 0; x < 10000; x++)
      ;
  }
}
