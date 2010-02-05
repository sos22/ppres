/* Various bits of logging which are useful primarily to figure out
   what's gone wrong from a core dump. */
#include <stddef.h>
#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_tooliface.h"
#include "libvex_guest_amd64.h"
#include "replay2.h"

/* We log all of the control commands received by this worker. */
static unsigned
nr_logged_control_commands;
static struct control_command *
command_log;
void
debug_control_command(const struct control_command *cc)
{
	nr_logged_control_commands++;
	command_log = VG_(realloc)("command log",
				   command_log,
				   sizeof(struct control_command) * nr_logged_control_commands);
	command_log[nr_logged_control_commands-1] = *cc;
}


/* We keep a buffer of the last few trace messages, even if we're not
   in trace mode. */
struct tracelog {
	unsigned code;
	unsigned nr_args;
	unsigned long args[];
};

#define TRACE_ARENA_SIZE 4088
struct tracelog_arena {
	unsigned used;
	unsigned char body[TRACE_ARENA_SIZE];
};

#define NR_TRACE_ARENAS 16
static struct tracelog_arena
tracelog[NR_TRACE_ARENAS];
static unsigned
current_trace_arena;

static struct tracelog *
get_tracelog(unsigned nr_args)
{
	struct tracelog_arena *arena;
	unsigned desired_size;
	struct tracelog *res;

	desired_size = sizeof(struct tracelog) + nr_args * sizeof(unsigned long);
	tl_assert(desired_size < TRACE_ARENA_SIZE);
	arena = &tracelog[current_trace_arena % NR_TRACE_ARENAS];
	if (arena->used + desired_size > TRACE_ARENA_SIZE) {
		current_trace_arena++;
		arena = &tracelog[current_trace_arena % NR_TRACE_ARENAS];
		arena->used = 0;
	}
	res = (struct tracelog *)(arena->body + arena->used);
	arena->used += desired_size;
	VG_(memset)(res, 0x1b, desired_size);
	return res;
}

void
_debug_trace_data(unsigned code, unsigned nr_args, const unsigned long *args)
{
	struct tracelog *l;

	l = get_tracelog(nr_args);
	l->code = code;
	l->nr_args = nr_args;
	VG_(memcpy)(l->args, args, nr_args * 8);
}
