#define DEBUG(fmt, args...) //VG_(printf)(fmt, ## args)

#define RECORD_BLOCK_SIZE 16384
#define MAX_RECORD_SIZE 4096

struct record_header {
	unsigned cls;
	unsigned size;
	unsigned tid;
};

struct footstep_record {
#define RECORD_footstep 1
	Word rip;
	Word rdx;
	Word rcx;
	Word rax;
};

struct syscall_record {
#define RECORD_syscall 2
	UInt syscall_nr;
	SysRes syscall_res;
};

struct memory_record {
#define RECORD_memory 3
	void *ptr;
	/* Followed by lots more data */
};

struct rdtsc_record {
#define RECORD_rdtsc 4
	ULong stashed_tsc;
};

struct mem_read_record {
#define RECORD_mem_read 5
	void *ptr;
	/* Followed by the data */
};

struct mem_write_record {
#define RECORD_mem_write 6
	void *ptr;
	/* Followed by the data */
};
