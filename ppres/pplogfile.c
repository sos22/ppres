/* Simple thing for pretty-printing the logfile */
#include <ctype.h>
#include <err.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef unsigned long Word;
typedef unsigned int UInt;
typedef int Int;
typedef unsigned long ULong;
typedef unsigned long UWord;
#define False false
#define True true
typedef bool Bool;
typedef struct {
	UWord _val;
	Bool  _isError;
} SysRes;

typedef struct sigaction sigaction_t;
#include "ppres.h"

#define STR2(x) #x
#define STR(x) STR2(x)

static void *
read_record(FILE *f, struct record_header *hp)
{
	void *work;

	if (fread(hp, sizeof(*hp), 1, f) != 1)
		return NULL;
	work = malloc(hp->size - sizeof(*hp));
	if (fread(work, 1, hp->size - sizeof(*hp), f) !=
	    hp->size - sizeof(*hp)) {
		free(work);
		return NULL;
	}
	return work;
}

static void
dump_bytes(const void *base, unsigned size)
{
	const unsigned char *p = base;
	unsigned to_dump;
	unsigned x;
	if (size < 16)
		to_dump = size;
	else
		to_dump = 16;
	for (x = 0; x < to_dump; x++)
		printf(" %02x(%c)", p[x], isprint(p[x]) ? p[x] : '.');
	if (size != to_dump) {
		printf("... (%d more)", size - to_dump);
	} else {
		switch (size) {
		case 2:
			printf(" = 0x%x", *(unsigned short *)base);
			break;
		case 4:
			printf(" = 0x%x", *(unsigned int *)base);
			break;
		case 8:
			printf(" = 0x%lx", *(unsigned long *)base);
			break;
		case 16:
			printf(" = 0x%lx:0x%lx",
			       ((unsigned long *)base)[0],
			       ((unsigned long *)base)[1]);
			break;
		}
	}
}

int
main(int argc, char *argv[])
{
	FILE *f;
	struct record_header h;
	void *payload;
	unsigned record_nr;
	unsigned epoch;

	f = fopen(argv[1], "r");
	if (!f)
		err(1, "opening %s", argv[1]);
	record_nr = 0;
	epoch = 0;
	while (1) {
		payload = read_record(f, &h);
		if (!payload) {
			if (feof(f))
				break;
			err(1, "reading from %s", argv[1]);
		}
		printf("%10d:%d:%d: ", record_nr, epoch, h.tid);
		switch (h.cls) {
		case RECORD_footstep: {
			struct footstep_record *fr = payload;
			printf("footstep: rip = %lx, %s = %lx, %s = %lx, %s = %lx, %s = %lx, %s = %lx\n",
			       fr->rip,
			       STR(FOOTSTEP_REG_0_NAME),
			       fr->FOOTSTEP_REG_0_NAME,
			       STR(FOOTSTEP_REG_1_NAME),
			       fr->FOOTSTEP_REG_1_NAME,
			       STR(FOOTSTEP_REG_2_NAME),
			       fr->FOOTSTEP_REG_2_NAME,
			       STR(FOOTSTEP_REG_3_NAME),
			       fr->FOOTSTEP_REG_3_NAME,
			       STR(FOOTSTEP_REG_4_NAME),
			       fr->FOOTSTEP_REG_3_NAME);
			break;
		}
		case RECORD_syscall: {
			struct syscall_record *sr = payload;
			printf("syscall: %d, res %ld (error %d), arg1 %lx, arg2 %lx, arg3 %lx\n",
			       sr->syscall_nr, sr->syscall_res._val,
			       sr->syscall_res._isError,
			       sr->arg1, sr->arg2, sr->arg3);
			epoch++;
			break;
		}
		case RECORD_memory: {
			struct memory_record *mr = payload;
			printf("memory: %p", mr->ptr);
			dump_bytes(mr + 1, h.size - sizeof(h) - sizeof(*mr));
			printf("\n");
			break;
		}
		case RECORD_rdtsc: {
			struct rdtsc_record *rr = payload;
			printf("rdtsc: %lx\n", rr->stashed_tsc);
			epoch++;
			break;
		}
		case RECORD_mem_read: {
			struct mem_read_record *mrr = payload;
			printf("mem read: 0x%lx", mrr->ptr);
			dump_bytes(mrr + 1, h.size - sizeof(h) - sizeof(*mrr));
			printf("\n");
			epoch++;
			break;
		}
		case RECORD_mem_write: {
			struct mem_write_record *mwr = payload;
			printf("mem write: 0x%lx", mwr->ptr);
			dump_bytes(mwr + 1, h.size - sizeof(h) - sizeof(*mwr));
			printf("\n");
			epoch++;
			break;
		}
		case RECORD_new_thread: {
			printf("new thread\n");
			break;
		}
		case RECORD_thread_blocking: {
			printf("thread blocking\n");
			break;
		}
		case RECORD_thread_unblocked: {
			printf("thread unblocked.\n");
			break;
		}
		case RECORD_client: {
			struct client_req_record *crr = payload;
			printf("client request %lx\n", crr->flavour);
			epoch++;
			break;
		}
		case RECORD_signal: {
			struct signal_record *sr = payload;
			printf("signal %d at rip %lx, err %lx, addr %lx\n",
			       sr->signo, sr->rip, sr->err, sr->virtaddr);
			break;
		}
		default:
			printf("record cls %d\n", h.cls);
			break;
		}
		free(payload);
		record_nr++;
	}
	fclose(f);
	return 0;
}
