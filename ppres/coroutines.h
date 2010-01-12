
struct coroutine {
	unsigned long rbx;
	unsigned long rsp;
	unsigned long rbp;
	unsigned long r12;
	unsigned long r13;
	unsigned long r14;
	unsigned long r15;

	/* These are call-clobbered, so don't really need to be saved,
	   but they're used to pass in the parameters to the start
	   routine. */
	unsigned long rdi; /* 56 */
	unsigned long rsi; /* 64 */
	unsigned long rdx; /* 72 */
	unsigned long rcx; /* 80 */
	unsigned long r8; /* 88 */
	unsigned long r9; /* 96 */

	unsigned long in_use; /* 104 */
	const char *name;
};

void run_coroutine(struct coroutine *me, const struct coroutine *target);
void make_coroutine(struct coroutine *out,
		    const char *name,
		    void *stack,
		    unsigned stack_size,
		    void *f,
		    unsigned nr_args,
		    ...);
void initialise_coroutine(struct coroutine *cr, const char *name);

void coroutine_bad_return_c(struct coroutine *cr);
void activate_bad_coroutine(struct coroutine *src, struct coroutine *dest);
void deactivate_bad_coroutine(struct coroutine *src, struct coroutine *dest);
