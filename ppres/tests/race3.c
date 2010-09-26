#include <sys/types.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
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
    if (r1 != r2)
      *(unsigned *)0xf001 = 5;
  }
}

int
main()
{
  pthread_t pthr;

  sleep(10);
  printf("Hello\n");
  pthread_create(&pthr, NULL, thread, NULL);
  while (1) {
    global++;
  }
}
