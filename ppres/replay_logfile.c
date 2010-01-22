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

	VG_(memset)(res, 0, sizeof(*res));
	open_res = VG_(open)(fname, VKI_O_RDONLY, 0);
	res->fd = sr_Res(open_res);
	res->current_chunk = VG_(malloc)("logbuffer",
					 RECORD_BLOCK_SIZE);
	res->peek_chunk = VG_(malloc)("logbuffer",
				      RECORD_BLOCK_SIZE);
	res->offset_in_current_chunk = 0;
	res->avail_in_current_chunk = 0;
}

void
close_logfile(struct record_consumer *rc)
{
	VG_(close)(rc->fd);
	VG_(free)(rc->current_chunk);
	VG_(free)(rc->peek_chunk);
}

static Bool
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
	rc->offset_in_file += actually_read;
	if (actually_read == 0)
		return False;
	else
		return True;
}

struct record_header *
get_current_record(struct record_consumer *rc)
{
	struct record_header *res;

	if (rc->offset_in_current_chunk + sizeof(struct record_header) >
	    rc->avail_in_current_chunk) {
		if (!advance_chunk(rc))
			return NULL;
	}
	tl_assert(rc->avail_in_current_chunk >=
		  rc->offset_in_current_chunk + sizeof(struct record_header));
	res = rc->current_chunk + rc->offset_in_current_chunk;
	if (rc->offset_in_current_chunk + res->size >
	    rc->avail_in_current_chunk) {
		if (!advance_chunk(rc))
			return NULL;
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

OffT
logfile_tell(struct record_consumer *rc)
{
	return rc->offset_in_file + rc->offset_in_current_chunk - rc->avail_in_current_chunk;
}

Bool
peek_record(struct record_consumer *rc, OffT ptr, struct record_header *rh)
{
	OffT start;
	Int r;
	OffT gone;

	if (ptr - rc->offset_in_file + sizeof(*rh) + rc->avail_in_current_chunk <
	    rc->avail_in_current_chunk) {
		VG_(memcpy)(rh,
			    rc->current_chunk + ptr - rc->offset_in_file + rc->avail_in_current_chunk,
			    sizeof(*rh));
		return True;
	}

	if (ptr >= rc->peek_chunk_start &&
	    ptr + sizeof(*rh) <= rc->peek_chunk_start + rc->peek_chunk_size) {
		VG_(memcpy)(rh,
			    rc->peek_chunk + ptr - rc->peek_chunk_start,
			    sizeof(*rh));
		return True;
	}

	rc->peek_chunk_size = 0;

	start = VG_(lseek)(rc->fd, 0, VKI_SEEK_CUR);
	gone = VG_(lseek)(rc->fd, ptr, VKI_SEEK_SET);
	tl_assert(gone == ptr);
	r = VG_(read)(rc->fd, rc->peek_chunk, RECORD_BLOCK_SIZE);
	VG_(lseek)(rc->fd, start, VKI_SEEK_SET);

	if (r <= 0)
		return False;
	tl_assert(r >= sizeof(*rh));
	rc->peek_chunk_size = r;
	rc->peek_chunk_start = ptr;

	VG_(memcpy)(rh, rc->peek_chunk, sizeof(*rh));
	tl_assert(rh->cls <= RECORD_MAX_CLASS);
	tl_assert(rh->size >= sizeof(*rh));
	if (r == sizeof(*rh))
		return True;
	else
		return False;
}

void
logfile_reset_file_ptr(struct record_consumer *lf)
{
	VG_(lseek)(lf->fd, lf->offset_in_file, VKI_SEEK_SET);
}

