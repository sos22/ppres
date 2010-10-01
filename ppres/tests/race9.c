#include <pthread.h>
#include <stdio.h>
#include <assert.h>

volatile unsigned *volatile global1;

void
dotest()
{
  volatile unsigned *l1;

  l1 = global1;
  if (l1)
    assert(*l1 == 5);
}

void *
thread(void *ign)
{
  while (1)
    dotest();
}

int
main()
{
  pthread_t pthr;
  volatile unsigned local;

  local = 7;
  pthread_create(&pthr, NULL, thread, NULL);
  while (1) {
    local = 5;
    global1 = &local;
    global1 = NULL;
    local = 7;
  }
}
