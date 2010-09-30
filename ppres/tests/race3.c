#include <sys/types.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>

volatile unsigned global;

void dotest()
{
  unsigned r1;
  unsigned r2;
  r1 = global;
  r2 = global;
  if (r1 != r2)
    *(unsigned *)0xf001 = 5;
}

static void *
thread(void *ignore)
{
  while (1)
    dotest();
}

int
main()
{
  pthread_t pthr;
  unsigned x;

  pthread_create(&pthr, NULL, thread, NULL);
  while (1) {
    global++;
  }
}
