/* Various #defines to make it easier to run bits of the program
   stand-alone, which is handy for unit tests. */
#ifdef UNIT_TEST
#include <sys/types.h>
#include <sys/fcntl.h>
#include <assert.h>
#include <err.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

typedef bool Bool;
typedef off_t OffT;
typedef signed char Char;
typedef int Int;
#define True true
#define False false

typedef long SysRes;

#define sr_Res(x) (x)

#define VG_(x) x

#define VKI_O_RDWR O_RDWR
#define VKI_O_RDONLY O_RDONLY
#define VKI_O_WRONLY O_WRONLY
#define VKI_O_CREAT O_CREAT
#define VKI_O_TRUNC O_TRUNC

#define VKI_SEEK_END SEEK_END
#define VKI_SEEK_SET SEEK_SET
#define VKI_SEEK_CUR SEEK_CUR

#define malloc(_, x) malloc(x)
#define open(a, b, c) open((const char *)(a), (b), (c))

#define tl_assert assert
#define tool_panic(x) errx(1, "%s", (x));
#endif
