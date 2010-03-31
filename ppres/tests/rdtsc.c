#include <stdio.h>

int
main()
{
  unsigned long out1, out2;
  asm ("rdtsc"
       : "=a" (out1), "=d" (out2));
  printf("tsc %lx\n",out1 | (out2 << 32));
  return 0;
}
