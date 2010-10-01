#include <pthread.h>
#include <stdio.h>
#include <assert.h>

volatile unsigned global1;
volatile unsigned global2;

void
dotest()
{
  unsigned l1, l2;

  l1 = global1;
  l2 = global2;
  assert(l1 == l2);
}

void
thread()
{
  while (1)
    dotest();
}

int
main()
{
  pthread_t pthr;

  pthread_create(&pthr, NULL, thread, NULL);
  while (1) {
    global1 = 5;
    global2 = 5;
    global1 = 7;
    global2 = 7;
  }
}
