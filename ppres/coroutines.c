#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "coroutines.h"

#define DO_REG(name, offset)			        \
	"movq %" name ", " STRINGIFY(offset)"(%rdi)\n"	\
        RESTORE_REG(name, offset)

#define RESTORE_REG(name, offset)			\
	"movq " STRINGIFY(offset) "(%rsi), %" name "\n"

#define STRINGIFY(x) #x
#define STRINGIFY2(x) STRINGIFY(x)
asm ( ".text\n"
      ".globl run_coroutine\n"
      "run_coroutine:\n"
		/* %rdi points at the current routine save area, %rsi
		   points at the target routine. */
		DO_REG("rbx", 0)
		DO_REG("rsp", 8)
		DO_REG("rbp", 16)
		DO_REG("r12", 24)
		DO_REG("r13", 32)
		DO_REG("r14", 40)
		DO_REG("r15", 48)
		RESTORE_REG("r9", 96)
		RESTORE_REG("r8", 88)
		RESTORE_REG("rcx", 80)
		RESTORE_REG("rdx", 72)
		RESTORE_REG("rdi", 56) /* Must be after all DO_REG */
		RESTORE_REG("rsi", 64) /* Must be last */
		"ret\n"
      ".previous\n"
);

/* Unusual calling convention: we pop arguments from the stack until
   we see the magic, and then use the next argument as a char *.  This
   is necessary because there are varargs on the stack in the way, and
   we don't know how many. */
#define COROUTINE_NAME_MAGIC 0xdeadbeef
extern unsigned coroutine_bad_return;

asm ( ".text\n"
      "coroutine_bad_return:"
		"popq %rdi\n"
                "cmpl $" STRINGIFY2(COROUTINE_NAME_MAGIC)", %edi\n"
                "jne coroutine_bad_return\n"
                "popq %rdi\n"
		"jmp coroutine_bad_return_c\n"
      ".previous\n" );

static void
push(struct coroutine *cr, const void *val)
{
	cr->rsp -= 8;
	*(const void **)cr->rsp = val;
}

void
make_coroutine(struct coroutine *out,
	       const char *name,
	       void *stack,
	       unsigned stack_size,
	       void *f,
	       unsigned nr_args,
	       ...)
{
	unsigned x;
	va_list args;

	memset(out, 0, sizeof(*out));
	out->rsp = (unsigned long)(stack + stack_size);
	push(out, name);
	push(out, (void *)COROUTINE_NAME_MAGIC);

	/* Set up arguments */
	va_start(args, nr_args);

	/* Register args */
	if (nr_args >= 1)
		out->rdi = va_arg(args, unsigned long);
	if (nr_args >= 2)
		out->rsi = va_arg(args, unsigned long);
	if (nr_args >= 3)
		out->rdx = va_arg(args, unsigned long);
	if (nr_args >= 4)
		out->rcx = va_arg(args, unsigned long);
	if (nr_args >= 5)
		out->r8 = va_arg(args, unsigned long);
	if (nr_args >= 6)
		out->r9 = va_arg(args, unsigned long);

	/* Stack args */
	if (nr_args > 6) {
		nr_args -= 6;
		out->rsp -= nr_args * 8;
		for (x = 0; x < nr_args; x++)
			((unsigned long *)out->rsp)[x] =
				va_arg(args, unsigned long);
	}

	push(out, &coroutine_bad_return);
	push(out, f);
}
