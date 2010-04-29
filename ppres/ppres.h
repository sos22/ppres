#define FOOTSTEP_REG_0_NAME RDI
#define FOOTSTEP_REG_0_OFFSET 0x38
#define FOOTSTEP_REG_1_NAME RDX
#define FOOTSTEP_REG_1_OFFSET 0x10
#define FOOTSTEP_REG_2_NAME CC_DEP2
#define FOOTSTEP_REG_2_OFFSET 144
#define FOOTSTEP_REG_3_NAME CC_NDEP
#define FOOTSTEP_REG_3_OFFSET 152
#define FOOTSTEP_REG_4_NAME RAX
#define FOOTSTEP_REG_4_OFFSET 0

#ifndef FOOTSTEP_REGS_ONLY

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
	Word FOOTSTEP_REG_0_NAME;
	Word FOOTSTEP_REG_1_NAME;
	Word FOOTSTEP_REG_2_NAME;
	Word FOOTSTEP_REG_3_NAME;
	Word FOOTSTEP_REG_4_NAME;
};

struct syscall_record {
#define RECORD_syscall 2
	UInt syscall_nr;
	SysRes syscall_res;
	UWord arg1;
	UWord arg2;
	UWord arg3;
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
	Word ptr;
	/* Followed by the data */
};

struct mem_write_record {
#define RECORD_mem_write 6
	Word ptr;
	/* Followed by the data */
};

/* No payload data */
#define RECORD_new_thread 7

/* No payload */
#define RECORD_thread_blocking 8

/* No payload */
#define RECORD_thread_unblocked 9

struct client_req_record {
#define RECORD_client 10
	UWord flavour;
};

struct signal_record {
#define RECORD_signal 11
	UWord rip;
	Int signo;
	UWord err;
	UWord virtaddr;
};

struct allocate_memory_record {
#define RECORD_allocate_memory 12
	UWord start;
	UWord size;
	UWord prot;
	UWord flags;
};

/* Uses VexGuestAMD64State as payload */
#define RECORD_initial_registers 13

#define RECORD_initial_brk 14
struct initial_brk_record {
#define RECORD_initial_brk 14
	UWord initial_brk;
};

#define RECORD_MAX_CLASS RECORD_initial_brk


struct index_record {
	unsigned long record_nr;
	unsigned long offset_in_file;
};

static inline int
IS_STACK(const void *ptr, unsigned long rsp)
{
	if ((unsigned long)ptr < (unsigned long)rsp - 128 ||
	    (unsigned long)ptr > (unsigned long)rsp + 16384)
		return False;
	else
		return True;
}

#endif /* !FOOTSTEP_REGS_ONLY */
