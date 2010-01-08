#define _LARGEFILE64_SOURCE
#include "pub_tool_basics.h"
#include "pub_tool_machine.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcfile.h"
#include "ppres.h"
#include "replay.h"

void
open_logfile(struct record_consumer *res,
	     const signed char *fname)
{
	SysRes open_res;

	open_res = VG_(open)(fname, VKI_O_RDONLY, 0);
	res->fd = sr_Res(open_res);
	res->current_chunk = VG_(malloc)("logbuffer",
					 RECORD_BLOCK_SIZE);
	res->offset_in_current_chunk = 0;
	res->avail_in_current_chunk = 0;
}

void
close_logfile(struct record_consumer *rc)
{
	VG_(close)(rc->fd);
	VG_(free)(rc->current_chunk);
}

static void
advance_chunk(struct record_consumer *rc)
{
	unsigned to_read;
	Int actually_read;

	tl_assert(rc->avail_in_current_chunk >= rc->offset_in_current_chunk);
	VG_(memmove)(rc->current_chunk,
		     rc->current_chunk + rc->offset_in_current_chunk,
		     rc->avail_in_current_chunk - rc->offset_in_current_chunk);
	rc->avail_in_current_chunk -= rc->offset_in_current_chunk;
	rc->offset_in_current_chunk = 0;
	to_read = RECORD_BLOCK_SIZE - rc->avail_in_current_chunk;
	actually_read =
		VG_(read)(rc->fd,
			  rc->current_chunk + rc->avail_in_current_chunk,
			  to_read);
	rc->avail_in_current_chunk += actually_read;
	if (actually_read == 0) {
		/* We've hit the end of the logfile.  That counts as
		 * success. */
		success();
		/* Don't get here */
	}
}

struct record_header *
get_current_record(struct record_consumer *rc)
{
	struct record_header *res;

	if (rc->offset_in_current_chunk + sizeof(struct record_header) >
	    rc->avail_in_current_chunk)
		advance_chunk(rc);
	tl_assert(rc->avail_in_current_chunk >=
		  rc->offset_in_current_chunk + sizeof(struct record_header));
	res = rc->current_chunk + rc->offset_in_current_chunk;
	if (rc->offset_in_current_chunk + res->size >
	    rc->avail_in_current_chunk) {
		advance_chunk(rc);
		res = rc->current_chunk + rc->offset_in_current_chunk;
	}
	tl_assert(rc->avail_in_current_chunk >=
		  rc->offset_in_current_chunk + sizeof(struct record_header));
	tl_assert(rc->avail_in_current_chunk >=
		  rc->offset_in_current_chunk + res->size);
	return res;
}

void
finish_this_record(struct record_consumer *rc)
{
	tl_assert(rc->avail_in_current_chunk >= rc->offset_in_current_chunk);
	rc->offset_in_current_chunk += get_current_record(rc)->size;
	tl_assert(rc->avail_in_current_chunk >= rc->offset_in_current_chunk);
}
