.global do_lock
.global do_unlock
	
#define SAVE_ALL_CLOBBERED	\
	pushf;			\
	pushq %rax;		\
	pushq %rcx;		\
	pushq %rdx;		\
	pushq %rsi;		\
	pushq %rdi;		\
	pushq %r8;		\
	pushq %r9;		\
	pushq %r10;		\
	pushq %r11

#define RESTORE_ALL_CLOBBERED	\
	popq %r11;		\
	popq %r10;		\
	popq %r9;		\
	popq %r8;		\
	popq %rdi;		\
	popq %rsi;		\
	popq %rdx;		\
	popq %rcx;		\
	popq %rax;		\
	popf
	
do_lock:
	SAVE_ALL_CLOBBERED
	call do_lock_c
	RESTORE_ALL_CLOBBERED
	ret

do_unlock:
	SAVE_ALL_CLOBBERED
	call do_unlock_c
	RESTORE_ALL_CLOBBERED
	ret
	