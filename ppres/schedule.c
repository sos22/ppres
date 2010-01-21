#define _LARGEFILE64_SOURCE
#ifndef UNIT_TEST
#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_mallocfree.h"
#endif

#include "unit_test.h"
#include "schedule.h"

#define SCHEDULE_WINDOW_SIZE 16384

#define SANITY_CHECK_SCHEDULE 0
#define SNAPSHOT_FREQUENCY 10

/* A schedule is just a list of schedule entries.  Each schedule entry
   represents the result of a non-deterministic choice, and is a pair
   (max, current), where current is the index of the option which is
   currently being explored and max is the largest valid index. */
struct schedule_entry {
	unsigned current_option;
	unsigned max_option;
};

static void
es_pread(struct execution_schedule *es,
	 void *buf,
	 unsigned buf_size,
	 OffT file_offset)
{
	unsigned read_so_far;
	Int read_this_time;

	VG_(lseek)(es->fd, file_offset, VKI_SEEK_SET);
	read_so_far = 0;
	while (read_so_far < buf_size) {
		read_this_time = VG_(read)(es->fd,
					   buf + read_so_far,
					   buf_size - read_so_far);
		tl_assert(read_this_time > 0);
		read_so_far += read_this_time;
	}
	tl_assert(read_so_far == buf_size);
}

#if SANITY_CHECK_SCHEDULE
static void
sanity_check_schedule(struct execution_schedule *es)
{
	OffT len;
	OffT ptr;
	struct schedule_entry se, *sep;

	len = VG_(lseek)(es->fd, 0, VKI_SEEK_END);
	tl_assert(len == es->file_size);
	tl_assert(len % sizeof(se) == 0);
	for (ptr = 0; ptr < len; ptr += sizeof(se)) {
		es_pread(es, &se, sizeof(se), ptr);
		tl_assert(se.max_option > 0);
		tl_assert(se.current_option <= se.max_option);
		ptr += sizeof(se);
	}

	if (!es->replay_mode) {
		/* This is necessary for the sanity check to work, but
		   is otherwise wrong. */
		tl_assert(!(es->window_offset_in_file % sizeof(se)));

		for (sep = es->window; sep < es->window + es->offset_in_window; sep++) {
			tl_assert(sep->max_option > 0);
			tl_assert(sep->current_option <= sep->max_option);
		}
	}

	tl_assert(es->replay_mode == False || es->replay_mode == True);
	tl_assert(es->offset_in_window <= es->avail_in_window);
	tl_assert(es->window_offset_in_file <= es->file_size);
	if (es->window_offset_in_file == es->file_size)
		tl_assert(!es->replay_mode);
}
#else
static void
sanity_check_schedule(struct execution_schedule *es)
{
}
#endif

void
open_execution_schedule(struct execution_schedule *es,
			const Char *filename)
{
	SysRes open_res;

	VG_(memset)(es, 0, sizeof(*es));

	open_res = VG_(open)((const Char *)filename, VKI_O_RDWR, 0);
	es->fd = sr_Res(open_res);
	es->window = VG_(malloc)("execution schedule arena",
				 SCHEDULE_WINDOW_SIZE);
	es->offset_in_window = 0;
	es->window_offset_in_file = 0;
	es->file_size = VG_(lseek)(es->fd, 0, VKI_SEEK_END);
	if (es->file_size == 0) {
		es->avail_in_window = SCHEDULE_WINDOW_SIZE;
		es->replay_mode = False;
	} else {
		es->avail_in_window = 0;
		es->replay_mode = True;
	}
	es->name = filename;
	sanity_check_schedule(es);
}

void
create_empty_execution_schedule(const Char *filename)
{
	SysRes open_res;
	open_res = VG_(open)((const Char *)filename,
			     VKI_O_RDWR | VKI_O_CREAT | VKI_O_TRUNC,
			     0600);
	VG_(close)(sr_Res(open_res));
}

/* True on success, False on failure. */
Bool
advance_schedule_to_next_choice(const Char *filename,
				OffT min_size)
{
	int fd;
	SysRes open_res;
	OffT ptr;
	struct schedule_entry buffer;
	int r;

	open_res = VG_(open)((const Char *)filename,
			     VKI_O_RDWR,
			     0);
	fd = sr_Res(open_res);
	ptr = VG_(lseek)(fd, 0, VKI_SEEK_END);
	if (ptr < min_size) {
		/* Someone truncated the schedule beyond the limit.
		   Fail out. */
		VG_(printf)("Schedule truncated to %lx, min size %lx, letting parent deal with it.\n",
			    ptr, min_size);
		return False;
	}
	while (ptr != min_size) {
		tl_assert(ptr > min_size);
		ptr -= sizeof(buffer);
		VG_(lseek)(fd, ptr, VKI_SEEK_SET);
		r = VG_(read)(fd, &buffer, sizeof(buffer));
		tl_assert(r == sizeof(buffer));
		tl_assert(buffer.max_option > 0);
		tl_assert(buffer.current_option <= buffer.max_option);
		if (buffer.current_option < buffer.max_option) {
			VG_(printf)("Advance choice at offset %lx, %d -> %d\n",
				    ptr, buffer.current_option,
				    buffer.current_option + 1);
			buffer.current_option++;
			VG_(lseek)(fd, ptr, VKI_SEEK_SET);
			VG_(write)(fd, &buffer, sizeof(buffer));
			VG_(ftruncate)(fd, ptr + sizeof(buffer));
			VG_(close)(fd);
			return True;
		}
	}
	return False;
}

static void
es_pwrite(struct execution_schedule *es,
	  const void *buf,
	  unsigned buf_size,
	  OffT file_offset)
{
	unsigned written_so_far;
	Int written_this_time;

	VG_(lseek)(es->fd, file_offset, VKI_SEEK_SET);
	written_so_far = 0;
	while (written_so_far < buf_size) {
		written_this_time = VG_(write)(es->fd,
					       buf + written_so_far,
					       buf_size - written_so_far);
		tl_assert(written_this_time > 0);
		written_so_far += written_this_time;
	}
	tl_assert(written_so_far == buf_size);
}

static void
flush_pending_writes(struct execution_schedule *es)
{
	if (es->replay_mode)
		return;
	es_pwrite(es, es->window, es->offset_in_window,
		  es->window_offset_in_file);
	es->window_offset_in_file += es->offset_in_window;
	es->file_size = es->window_offset_in_file;
	es->offset_in_window = 0;
}

void
close_execution_schedule(struct execution_schedule *es)
{
	sanity_check_schedule(es);
	flush_pending_writes(es);
	sanity_check_schedule(es);
	VG_(close)(es->fd);
	VG_(free)(es->window);
}

static void
advance_window(struct execution_schedule *es)
{
	unsigned to_read;

	sanity_check_schedule(es);
	if (es->replay_mode) {
		VG_(memmove)(es->window,
			     es->window + es->offset_in_window,
			     es->avail_in_window - es->offset_in_window);
		es->window_offset_in_file += es->offset_in_window;
		es->avail_in_window -= es->offset_in_window;
		es->offset_in_window = 0;
		tl_assert(es->window_offset_in_file <=
			  es->file_size);
		if (es->window_offset_in_file == es->file_size) {
			/* Hit end of schedule; go to exploration
			 * mode. */
			tl_assert(es->avail_in_window == 0);
			es->replay_mode = False;
			es->avail_in_window = SCHEDULE_WINDOW_SIZE;
		} else {
			to_read = SCHEDULE_WINDOW_SIZE - es->avail_in_window;
			if (to_read > es->file_size - es->window_offset_in_file)
				to_read = es->file_size - es->window_offset_in_file;
			es_pread(es,
				 es->window + es->avail_in_window,
				 to_read,
				 es->window_offset_in_file);
			es->avail_in_window += to_read;
			sanity_check_schedule(es);
			return;
		}
		sanity_check_schedule(es);
	}

	tl_assert(!es->replay_mode);
	tl_assert(es->avail_in_window == SCHEDULE_WINDOW_SIZE);
	tl_assert(es->window_offset_in_file == es->file_size);

	flush_pending_writes(es);
	sanity_check_schedule(es);
}

static struct schedule_entry *
get_schedule_entry(struct execution_schedule *es)
{
	struct schedule_entry *se;

	sanity_check_schedule(es);
	if (es->offset_in_window + sizeof(*se) > es->avail_in_window)
		advance_window(es);
	se = es->window + es->offset_in_window;
	es->offset_in_window += sizeof(*se);
	return se;
}

unsigned
make_nd_choice(struct execution_schedule *es,
	       unsigned max_allowed)
{
	struct schedule_entry *se;
	Bool snapshot;

	sanity_check_schedule(es);
	if (max_allowed == 0)
		return 0;

	if (es->failed) {
		if (es->replay_mode) {
			se = get_schedule_entry(es);
			tl_assert(se->max_option == max_allowed);
			sanity_check_schedule(es);
			return se->current_option;
		} else {
			return 0;
		}
	}

	se = get_schedule_entry(es);
	if (es->replay_mode) {
		tl_assert(se->max_option == max_allowed);
		sanity_check_schedule(es);
		return se->current_option;
	}
	se->max_option = max_allowed;
	se->current_option = 0;
	sanity_check_schedule(es);
	flush_pending_writes(es);
	sanity_check_schedule(es);

	es->nr_choices++;
	snapshot = (es->nr_choices % SNAPSHOT_FREQUENCY == 0);
	if (snapshot) {
		VG_(printf)("Taking a snapshot at choice %d\n",
			    es->nr_choices);

		/* Hack: rewind one slot and go back into replay mode
		   so that we advance properly when we come back to
		   this snapshot. */
		es->avail_in_window = 0;
		es->window_offset_in_file -= sizeof(*se);
		es->replay_mode = True;

		exploration_take_snapshot(es->name);

		/* Need to pick up any changes in the schedule's size
		   on disk. */
		es->file_size = VG_(lseek)(es->fd, 0, VKI_SEEK_END);

		se = get_schedule_entry(es);
		VG_(printf)("Snapshot going down branch %d at %lx\n",
			    se->current_option,
			    es->window_offset_in_file);
	}

	sanity_check_schedule(es);
	return se->current_option;
}

OffT
get_schedule_size(struct execution_schedule *sched)
{
	return sched->window_offset_in_file + sched->offset_in_window;
}

void
schedule_failed_before(struct execution_schedule *sched,
		       OffT cookie)
{
	sanity_check_schedule(sched);
	if (get_schedule_size(sched) <= cookie) {
		VG_(printf)("Not truncating schedule to %lx: it was already %lx\n",
			    cookie, get_schedule_size(sched));
		return;
	}
	flush_pending_writes(sched);
	sanity_check_schedule(sched);
	VG_(printf)("Truncating schedule to %lx bytes.  in replay %d, file size %lx, offset %lx + %x.\n",
		    cookie, sched->replay_mode, sched->file_size, sched->window_offset_in_file,
		    sched->offset_in_window);
	VG_(ftruncate)(sched->fd, cookie);
	sched->replay_mode = False;
	sched->failed = True;
	sched->file_size = cookie;
	sched->window_offset_in_file = 0;
	sched->avail_in_window = 0;
	sanity_check_schedule(sched);
}

#ifdef UNIT_TEST
#include <sys/wait.h>
#include <signal.h>

static void
run_nondet_computation()
{
	struct execution_schedule the_schedule;

	open_execution_schedule(&the_schedule,
				(Char *)"test_schedule");
	switch (make_nd_choice(&the_schedule, 4)) {
	case 0:
		printf("Branch 0\n");
		switch (make_nd_choice(&the_schedule, 2)) {
		case 0:
			printf("  Branch 0\n");
			exit(1);
		case 1:
			printf("  Branch 1\n");
			exit(1);
		case 2:
			printf("  Branch 2\n");
		default:
			abort();
		}
		abort();
	case 1:
		printf("Branch 1\n");
		raise(SIGSEGV);
		abort();
	case 2:
		printf("Branch 2\n");
		switch (make_nd_choice(&the_schedule, 0)) {
		case 0:
			printf("  Branch 0\n");
			exit(1);
			break;
		default:
			abort();
		}
		abort();
	case 3:
		printf("Branch 3; success.\n");
		exit(0);
	case 4:
		printf("Branch 4, something wrong.\n");
		abort();
	default:
		abort();
	}
}

int
main()
{
	pid_t child;
	int status;

	create_empty_execution_schedule((Char *)"test_schedule");

	while (1) {
		printf("Trying another schedule...\n");
		fflush(NULL);
		child = fork();
		if (child == 0) {
			run_nondet_computation();
			printf("run_nondet finished?\n");
			fflush(NULL);
			exit(1);
		}
		waitpid(child, &status, 0);
		if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
			printf("Found a valid schedule.\n");
			fflush(NULL);
			break;
		}
		printf("That schedule failed, trying another one...\n");
		fflush(NULL);
		advance_schedule_to_next_choice((Char *)"test_schedule");
	}

	return 0;
}
#endif
