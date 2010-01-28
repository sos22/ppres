/* A very simple CLI for the searcher, because automating it off the
   bat is too hard. */
#include <stddef.h>
#include <limits.h>

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_mallocfree.h"
#include "libvex_guest_amd64.h"
#include "valgrind.h"

#include "replay2.h"

struct command_response {
	int res;
};

/* Making the normal headers work with Valgrind's is a pain, so don't
   bother. */
struct msghdr {
        void *msg_name;
        int msg_namelen;
        void *msg_iov;
        size_t msg_iovlen;
        void *msg_control;
        size_t msg_controllen;
        unsigned msg_flags;
};
struct cmsghdr {
        size_t cmsg_len;
        int cmsg_level;
        int cmsg_type;
};
struct iovec {
	void  *iov_base;
	size_t iov_len;
};
#define SOL_SOCKET 1
#define SCM_RIGHTS 1
#define AF_UNIX 1
#define SOCK_STREAM 1

static void
send_fd(int parent_fd, int child_fd)
{
	struct msghdr mh;
	struct {
		struct cmsghdr hdr;
		int fd;
	} cmsg;
	int r;
	char buf;
	struct iovec iov;

	VG_(memset)(&mh, 0, sizeof(mh));
	mh.msg_control = &cmsg;
	mh.msg_controllen = sizeof(cmsg);

	/* Surprise! You need to send at least one byte of data along
	   with the control message, or the other end doesn't
	   unblock. */
	iov.iov_base = &buf;
	iov.iov_len = 1;
	buf = 9;

	mh.msg_iov = &iov;
	mh.msg_iovlen = 1;

	cmsg.hdr.cmsg_len = sizeof(cmsg);
	cmsg.hdr.cmsg_level = SOL_SOCKET;
	cmsg.hdr.cmsg_type = SCM_RIGHTS;
	cmsg.fd = child_fd;
	r = sendmsg(parent_fd, &mh, 0);
	if (r < 0)
		VG_(tool_panic)((Char *)"sending file descriptor");
}

int
do_snapshot(int parent_fd)
{
	int fds[2];
	struct command_response resp;
	long child;
	int r;

	r = socketpair(AF_UNIX, SOCK_STREAM, 0, fds);
	if (r < 0)
		VG_(tool_panic)((Char *)"error creating socket pair");
	child = my_fork();
	if (child < 0)
		VG_(tool_panic)((Char *)"forking snapshot");
	if (child == 0) {
		VG_(close)(fds[1]);
		VG_(close)(parent_fd);
		return fds[0];
	}
	VG_(close)(fds[0]);
	resp.res = 0;
	safeish_write(parent_fd, &resp, sizeof(resp));
	send_fd(parent_fd, fds[1]);
	VG_(close)(fds[1]);
	return parent_fd;
}

int
ui_loop(void)
{
	int child;
	int fds[2];
	int r;
	Char buf[16];
	Char *args[3] = { (Char *)"ppres/driver/UI",
			  buf,
			  NULL };

	r = socketpair(AF_UNIX, SOCK_STREAM, 0, fds);
	if (r < 0)
		VG_(tool_panic)((Char *)"Error creating socket pair");

	child = my_fork();
	if (child == 0) {
		VG_(close)(fds[1]);
		return fds[0];
	}
	VG_(close)(fds[0]);

	VG_(sprintf)(buf, "%d", fds[1]);

	VG_(execv)(args[0], args);

	VG_(tool_panic)((Char *)"Cannot exec driver!");
}
