/* Bits and bobs to do with the race detector. */
/* Despite the prefix, this has nothing to do with Y Yu's
   race detector called RaceTrack. */
#ifndef UNIT_TEST
#include "pub_tool_basics.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#endif

#include "unit_test.h"
#include "races.h"

typedef unsigned long epoch_t;

struct vector_clock {
	unsigned nr_threads;
	epoch_t *epochs;
};

struct memhash_node {
	struct memhash_node *next;
	Addr addr;
	Bool racy;
	struct vector_clock read_vc;
	struct vector_clock write_vc;
};

struct thread_clock {
	struct thread_clock *next;
	ThreadId tid;
	struct vector_clock local_clock;
};

#define NR_MEMHASH_BUCKETS 128

static inline int
HASH_ADDRESS(Addr addr)
{
	return (addr ^ (addr / NR_MEMHASH_BUCKETS)) % NR_MEMHASH_BUCKETS;
}

static struct memhash_node *
memhash[NR_MEMHASH_BUCKETS];

static struct thread_clock *
thread_clocks;

#define MAX(x, y) ((x) > (y) ? (x) : (y))

static struct memhash_node *
memhash_lookup(Addr addr, Bool populate)
{
	struct memhash_node **pprev, **head, *cursor;

	head = pprev = &memhash[HASH_ADDRESS(addr)];
	cursor = *pprev;
	while (cursor) {
		if (cursor->addr == addr)
			break;
		pprev = &cursor->next;
		cursor = *pprev;
	}
	if (!cursor) {
		if (!populate)
			return NULL;
		cursor = VG_(malloc)("memhash node", sizeof(*cursor));
		VG_(memset)(cursor, 0, sizeof(*cursor));
		cursor->addr = addr;
	}

	/* Pull-to-front */
	*pprev = cursor->next;
	cursor->next = *head;
	*head = cursor;

	return cursor;
}

static struct memhash_node *
memhash_lookup_populate(Addr addr)
{
	return memhash_lookup(addr, True);
}

static int
find_vc(Addr addr, struct vector_clock **read_vc, struct vector_clock **write_vc)
{
	struct memhash_node *mn;

	mn = memhash_lookup_populate(addr);
	*read_vc = &mn->read_vc;
	*write_vc = &mn->write_vc;
	return !mn->racy;
}

Bool
is_racy(Addr addr)
{
	struct memhash_node *mn;
	mn = memhash_lookup(addr, False);
	if (!mn)
		return False;
	return mn->racy;
}

static void
race_address(Addr addr)
{
	struct memhash_node *mn;
	mn = memhash_lookup_populate(addr);
	tl_assert(!mn->racy);
	mn->racy = 1;
	new_race_address(addr);
}

static void
read_after_write_race(Addr addr)
{
	race_address(addr);
}

static void
write_after_read_race(Addr addr)
{
	race_address(addr);
}

static void
write_after_write_race(Addr addr)
{
	race_address(addr);
}

static epoch_t
get_vc_slot(const struct vector_clock *vc, ThreadId slot)
{
	if (slot >= vc->nr_threads)
		return 0;
	else
		return vc->epochs[slot];
}

static void
set_vc_slot(struct vector_clock *vc, ThreadId slot, epoch_t val)
{
	if (slot >= vc->nr_threads) {
		vc->epochs = VG_(realloc)("vc epochs",
					  vc->epochs,
					  sizeof(epoch_t) * (slot + 1));
		vc->nr_threads = slot + 1;
	}
	vc->epochs[slot] = val;
}

static Bool
vector_clock_before(const struct vector_clock *before,
		    const struct vector_clock *after)
{
	unsigned x;
	Bool eq;

	eq = True;
	for (x = 0; x < MAX(before->nr_threads, after->nr_threads); x++) {
		if (get_vc_slot(before, x) > get_vc_slot(after, x))
			return False;
		if (get_vc_slot(before, x) < get_vc_slot(after, x))
			eq = False;
	}
	/* Two threads should never have equal vector clocks. */
	tl_assert(!eq);
	return True;
}

static void
vector_clock_lub(struct vector_clock *out,
		 const struct vector_clock *in)
{
	unsigned x;
	for (x = 0; x < MAX(out->nr_threads, in->nr_threads); x++) {
		if (get_vc_slot(out, x) < get_vc_slot(in, x))
			set_vc_slot(out, x, get_vc_slot(in, x));
	}
}

static void
read_byte(Addr addr, struct vector_clock *now, ThreadId this_thread)
{
	struct vector_clock *read_vc;
	struct vector_clock *write_vc;
	unsigned x;

	if (!find_vc(addr, &read_vc, &write_vc)) {
		/* This address doesn't participate in the race
		   detection protocol. */
		return;
	}

	if (!vector_clock_before(write_vc, now)) {
		read_after_write_race(addr);
	}

	set_vc_slot(read_vc, this_thread, get_vc_slot(now, this_thread));
	for (x = 0;
	     x < MAX(read_vc->nr_threads, now->nr_threads);
	     x++) {
		if (get_vc_slot(read_vc, x) > get_vc_slot(now, x))
			set_vc_slot(now, x, get_vc_slot(read_vc, x));
	}
}

static void
write_byte(Addr addr, struct vector_clock *now)
{
	struct vector_clock *read_vc;
	struct vector_clock *write_vc;

	if (!find_vc(addr, &read_vc, &write_vc))
		return;

	if (!vector_clock_before(write_vc, now)) {
		write_after_write_race(addr);
		return;
	}

	if (!vector_clock_before(read_vc, now)) {
		write_after_read_race(addr);
		return;
	}

	vector_clock_lub(write_vc, now);
}

static struct thread_clock *
find_tc(ThreadId thread)
{
	struct thread_clock *tc;

	for (tc = thread_clocks; tc; tc = tc->next)
		if (tc->tid == thread)
			return tc;
	tc = VG_(malloc)("thread clocks", sizeof(*tc));
	VG_(memset)(tc, 0, sizeof(*tc));
	tc->tid = thread;
	tc->next = thread_clocks;
	thread_clocks = tc;
	return tc;
}

static void
bump_epoch(struct thread_clock *tc)
{
	set_vc_slot(&tc->local_clock,
		    tc->tid,
		    get_vc_slot(&tc->local_clock,
				tc->tid) + 1);
}

void
racetrack_read_region(Addr start, unsigned size,  ThreadId this_thread)
{
	struct thread_clock *tc = find_tc(this_thread);
	unsigned x;
	bump_epoch(tc);
	for (x = 0; x < size; x++)
		read_byte(start + x, &tc->local_clock, this_thread);
}

void
racetrack_write_region(Addr start, unsigned size, ThreadId this_thread)
{
	struct thread_clock *tc = find_tc(this_thread);
	unsigned x;
	bump_epoch(tc);
	for (x = 0; x < size; x++)
		write_byte(start + x, &tc->local_clock);
}

/* This is run in the driver process when the child tells it to flag
   an address as racy.  We mark it as such in the *driver*'s memhash,
   which will then be picked up by every subsequently forked worker
   without us having to do anything. */
void
mark_address_as_racy(Addr addr)
{
	struct memhash_node *mn;
	mn = memhash_lookup_populate(addr);
	tl_assert(!mn->racy);
	mn->racy = 1;
}

void
dump_vector_clock(const struct vector_clock *vc)
{
	unsigned x;
	VG_(printf)("VC %p : %d threads, {", vc, vc->nr_threads);
	for (x = 0; x < vc->nr_threads; x++)
		VG_(printf)("%ld, ", vc->epochs[x]);
	VG_(printf)("}\n");
}

void
dump_memhash_node(const struct memhash_node *mn)
{
	VG_(printf)("Memhash node %p: addr %lx, racy %d\n",
		    mn, mn->addr, mn->racy);
	VG_(printf)("Read VC: ");
	dump_vector_clock(&mn->read_vc);
	VG_(printf)("Write VC: ");
	dump_vector_clock(&mn->write_vc);
}

void
dump_racetrack_state(void)
{
	unsigned x;
	const struct memhash_node *mn;

	for (x = 0; x < NR_MEMHASH_BUCKETS; x++)
		for (mn = memhash[x]; mn; mn = mn->next)
			dump_memhash_node(mn);
}


#ifdef UNIT_TEST
int
main()
{
	tl_assert(!is_racy(5));
	racetrack_read_region(5, 1, 0);
	tl_assert(!is_racy(5));
	racetrack_write_region(5, 1, 0);
	tl_assert(!is_racy(5));
	racetrack_write_region(5, 1, 0);
	tl_assert(!is_racy(5));
	racetrack_read_region(5, 1, 1);
	tl_assert(is_racy(5));

	tl_assert(!is_racy(6));
	racetrack_read_region(6, 1, 0);
	racetrack_read_region(6, 1, 1);
	tl_assert(!is_racy(6));
	racetrack_write_region(6, 1, 2);
	tl_assert(is_racy(6));

	tl_assert(is_racy(5));

	printf("Done.\n");
	dump_racetrack_state();
	return 0;
}
#endif
