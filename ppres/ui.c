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
#include "pub_tool_mallocfree.h"
#include "valgrind.h"

#include "replay2.h"

#define ROOT_SNAPSHOT 0

struct command {
	enum {
		COMMAND_exit = 0xf001,
		COMMAND_whereami,
		COMMAND_snapshot,
		COMMAND_list_snapshots,
		COMMAND_kill_snapshot,
		COMMAND_activate_snapshot,
		COMMAND_run,
		COMMAND_trace,
		COMMAND_runm
	} cmd;
	union {
		struct {
			long id;
		} kill_snapshot;
		struct {
			long id;
		} activate_snapshot;
		struct {
			long nr;
		} run;
		struct {
			long nr;
		} trace;
		struct {
			long thread;
			long nr;
		} runm;
	} u;
};

struct history_entry {
	enum {
		HISTORY_run = 0xdead,
		HISTORY_runm
	} type;
	union {
		struct {
			long count;
		} run;
		struct {
			long thread;
			long count;
		} runm;
	} u;
};

struct history {
	unsigned nr_entries;
	struct history_entry *entries;
};

struct snapshot {
	struct snapshot *prev;
	struct snapshot *next;
	int controlling_fd;
	int id;
	struct history history;
};

struct worker {
	int controlling_fd;
	struct history history;
};

static struct snapshot *
root_snapshot;
static struct worker *
current_worker;

static int
strcmp(const char *a, const char *b)
{
	return VG_(strcmp)((Char *)a, (Char *)b);
}

static char *
tokenize(char **cursorp)
{
	char *cursor = *cursorp;
	char *res = cursor;

	if (!*cursor)
		return NULL;
	while (*cursor && *cursor != ' ' && *cursor != '\t')
		cursor++;
	if (*cursor) {
		*cursor = 0;
		*cursorp = cursor + 1;
	} else {
		*cursorp = cursor;
	}
	return res;
}

static Bool
my_strtol(long *out, const char *buf)
{
	long r;

	r = 0;
	*out = 0;
	while (buf[0]) {
		if (buf[0] < '0' || buf[0] > '9')
			return False;
		if (r >= LONG_MAX / 10)
			return False;
		r = r * 10 + buf[0] - '0';
		buf++;
	}
	*out = r;
	return True;
}

static void
strip(char *buf)
{
	char *end;
	for (end = buf; end[0]; end++)
		;
	end--;
	while (end >= buf &&
	       (end[0] == '\n' || end[0] == '\r' || end[0] == ' ' || end[0] == '\t'))
		end--;
	end[1] = 0;
}

static void
read_command(struct command *cmd)
{
	char buf[4097];
	char *verb;
	char *args;
	char *thread;
	Int r;

retry:
	VG_(printf)("> ");
	r = VG_(read)(0, buf, sizeof(buf) - 1);
	if (r <= 0) {
		VG_(printf)("Error %d reading command", r);
		my__exit(1);
	}
	buf[r] = 0;
	strip(buf);

	args = buf;
	verb = tokenize(&args);
	if (!verb)
		goto retry;

	if (!strcmp(verb, "exit") ||
	    !strcmp(verb, "quit")) {
		cmd->cmd = COMMAND_exit;
	} else if (!strcmp(verb, "loc") ||
		   !strcmp(verb, "whereami")) {
		cmd->cmd = COMMAND_whereami;
	} else if (!strcmp(verb, "snapshot")) {
		cmd->cmd = COMMAND_snapshot;
	} else if (!strcmp(verb, "ls")) {
		cmd->cmd = COMMAND_list_snapshots;
	} else if (!strcmp(verb, "kill")) {
		cmd->cmd = COMMAND_kill_snapshot;
		if (!my_strtol(&cmd->u.kill_snapshot.id, args)) {
			VG_(printf)("kill command needs a snapshot id\n");
			goto retry;
		}
		if (cmd->u.kill_snapshot.id == ROOT_SNAPSHOT) {
			VG_(printf)("can't kill the root snapshot\n");
			goto retry;
		}
	} else if (!strcmp(verb, "activate")) {
		cmd->cmd = COMMAND_activate_snapshot;
		if (!my_strtol(&cmd->u.activate_snapshot.id, args)) {
			VG_(printf)("activate command needs a snapshot id\n");
			goto retry;
		}
	} else if (!strcmp(verb, "run")) {
		cmd->cmd = COMMAND_run;
		if (!*args) {
			cmd->u.run.nr = -1;
		} else if (!my_strtol(&cmd->u.run.nr, args)) {
			VG_(printf)("run commands needs, at most, a record count\n");
			goto retry;
		}
	} else if (!strcmp(verb, "trace")) {
		cmd->cmd = COMMAND_trace;
		if (!*args) {
			cmd->u.trace.nr = -1;
		} else if (!my_strtol(&cmd->u.trace.nr, args)) {
			VG_(printf)("trace commands needs, at most, a record count\n");
			goto retry;
		}
	} else if (!strcmp(verb, "runm")) {
		cmd->cmd = COMMAND_runm;
		thread = tokenize(&args);
		if (!my_strtol(&cmd->u.runm.thread, thread)) {
			VG_(printf)("runm commands needs a thread id\n");
			goto retry;
		}
		if (!my_strtol(&cmd->u.runm.nr, args)) {
			VG_(printf)("runm commands needs an access count\n");
			goto retry;
		}
	} else {
		VG_(printf)("Bad command %s\n", verb);
		goto retry;
	}
}

struct command_response {
	int res;
};

static long
_send_command(int fd, unsigned command, unsigned long *args,
	      unsigned nr_args)
{
	struct command_header ch;
	struct command_response res;

	ch.command = command;
	ch.nr_args = nr_args;
	safeish_write(fd, &ch, sizeof(ch));
	if (nr_args)
		safeish_write(fd, args, sizeof(args[0]) * nr_args);
	safeish_read(fd, &res, sizeof(res));
	return res.res;
}
#define send_command(_whom, _cmd, ...)		  	          \
	({							  \
	unsigned long args[] = {__VA_ARGS__};			  \
	_send_command(_whom->controlling_fd, _cmd, args,          \
                      sizeof(args)/sizeof(args[0]));		  \
	 })

#define SNAPSHOT_KILL 0xabcd
#define SNAPSHOT_ACTIVATE 0xabce

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

static int
recv_fd(int parent_fd)
{
	struct msghdr mh;
	struct {
		struct cmsghdr hdr;
		int fd;
	} cmsg;
	char buf;
	struct iovec iov;

	VG_(memset)(&mh, 0, sizeof(mh));
	mh.msg_control = &cmsg;
	mh.msg_controllen = sizeof(cmsg);
	mh.msg_iov = &iov;
	mh.msg_iovlen = 1;
	iov.iov_base = &buf;
	iov.iov_len = 1;

	if (recvmsg(parent_fd, &mh, 0) < 0)
		VG_(tool_panic)((Char *)"receiving file descriptor");
	tl_assert(cmsg.hdr.cmsg_len == sizeof(cmsg));
	tl_assert(cmsg.hdr.cmsg_level == SOL_SOCKET);
	tl_assert(cmsg.hdr.cmsg_type == SCM_RIGHTS);
	return cmsg.fd;
}

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
	VG_(printf)("sendmsg fd %d said %d\n", child_fd, r);
	if (r < 0)
		VG_(tool_panic)((Char *)"sending file descriptor");
}

static void
kill_snapshot(struct snapshot *ss)
{
	if (send_command(ss, SNAPSHOT_KILL))
		VG_(tool_panic)((Char *)"Failed to kill snapshot");
	if (ss->prev)
		ss->prev->next = ss->next;
	else
		root_snapshot = ss->next;
	if (ss->next)
		ss->next->prev = ss->prev;
	VG_(close)(ss->controlling_fd);
	VG_(free)(ss->history.entries);
	VG_(free)(ss);
}

static void
dump_history(const struct history *h)
{
	unsigned x;
	for (x = 0; x < h->nr_entries; x++) {
		switch (h->entries[x].type) {
		case HISTORY_run:
			VG_(printf)("\tRUN %ld\n",
				    h->entries[x].u.run.count);
			break;
		case HISTORY_runm:
			VG_(printf)("\tRUNM %ld %ld\n",
				    h->entries[x].u.runm.thread,
				    h->entries[x].u.runm.count);
			break;
		default:
			VG_(tool_panic)((Char *)"history corrupted");
		}
	}
}

static void
duplicate_history(struct history *dest, const struct history *src)
{
	dest->nr_entries = src->nr_entries;
	dest->entries = VG_(malloc)("history", sizeof(dest->entries[0]) * dest->nr_entries);
	VG_(memcpy)(dest->entries, src->entries, sizeof(dest->entries[0]) * dest->nr_entries);
}

static struct snapshot *
take_snapshot(struct worker *worker)
{
	int fd;
	struct snapshot *work;
	static int next_snapshot_ident = 1;

	if (send_command(worker, WORKER_SNAPSHOT)) {
		VG_(printf)("Failed to take snapshot");
		return NULL;
	}

	fd = recv_fd(worker->controlling_fd);
	work = VG_(malloc)("snapshot", sizeof(*work));
	VG_(memset)(work, 0, sizeof(*work));
	work->controlling_fd = fd;
	work->id = next_snapshot_ident++;
	duplicate_history(&work->history, &worker->history);

	work->next = NULL;
	work->prev = root_snapshot;
	if (root_snapshot->next)
		root_snapshot->next->prev = work;
	root_snapshot->next = work;

	return work;
}

static struct snapshot *
find_snapshot(int id)
{
	struct snapshot *ss;

	for (ss = root_snapshot; ss && ss->id != id; ss = ss->next)
		;
	return ss;
}

static struct worker *
activate_snapshot(struct snapshot *ss)
{
	struct worker *worker;

	worker = VG_(malloc)("worker", sizeof(*worker));
	VG_(memset)(worker, 0, sizeof(*worker));
	duplicate_history(&worker->history, &ss->history);

	if (send_command(ss, SNAPSHOT_ACTIVATE)) {
		VG_(printf)("Failed to activate snapshot\n");
		return NULL;
	} else {
		worker->controlling_fd = recv_fd(ss->controlling_fd);
		return worker;
	}
}

static void
kill_worker(struct worker *worker)
{
	if (send_command(worker, WORKER_KILL))
		VG_(tool_panic)((Char *)"failed to kill worker");
	VG_(close)(worker->controlling_fd);
	VG_(free)(worker);
}

static void
history_append(struct history *h, struct history_entry he)
{
	struct history_entry *new;
	h->nr_entries++;
	new = VG_(realloc)("history buf", h->entries,
			   h->nr_entries * sizeof(he));
	new[h->nr_entries-1] = he;
	h->entries = new;
	VG_(printf)("Added history entry %d\n",
		    h->nr_entries - 1);
}

static void
run_worker(struct worker *worker, long nr_steps)
{
	if (send_command(worker, WORKER_RUN, nr_steps))
		VG_(printf)("Can't run worker for %ld steps\n", nr_steps);
	history_append(&worker->history,
		       ((struct history_entry){.type = HISTORY_run,
				       .u = { .run = { .count = nr_steps}}}));
}

static void
trace_worker(struct worker *worker, long nr_steps)
{
	if (send_command(worker, WORKER_TRACE, nr_steps))
		VG_(printf)("Can't trace worker for %ld steps\n", nr_steps);
	history_append(&worker->history,
		       ((struct history_entry){.type = HISTORY_run,
				       .u = { .run = { .count = nr_steps}}}));
}

static void
run_m_worker(struct worker *worker, long thread, long nr_steps)
{
	if (send_command(worker, WORKER_RUNM, thread, nr_steps))
		VG_(printf)("Can't run thread %ld for %ld memory operations\n",
			    thread, nr_steps);
	history_append(&worker->history,
		       ((struct history_entry){.type = HISTORY_runm,
				       .u = { .runm = { .thread = thread,
							.count = nr_steps}}}));
}

static void
run_command(const struct command *cmd)
{
	struct snapshot *s;

	switch (cmd->cmd) {
	case COMMAND_exit:
		while (root_snapshot)
			kill_snapshot(root_snapshot);
		if (current_worker)
			kill_worker(current_worker);
		my__exit(0);
	case COMMAND_whereami:
		if (!current_worker) {
			VG_(printf)("No current worker.\n");
		} else {
			dump_history(&current_worker->history);
		}
		break;
	case COMMAND_snapshot:
		if (!current_worker) {
			VG_(printf)("No current worker.\n");
		} else {
			s = take_snapshot(current_worker);
			if (s)
				VG_(printf)("%d\n", s->id);
		}
		break;
	case COMMAND_list_snapshots:
		for (s = root_snapshot; s; s = s->next)
			VG_(printf)("%d\n", s->id);
		break;
	case COMMAND_kill_snapshot:
		s = find_snapshot(cmd->u.kill_snapshot.id);
		if (!s) {
			VG_(printf)("No snapshot %ld\n", cmd->u.kill_snapshot.id);
		} else {
			kill_snapshot(s);
		}
		break;
	case COMMAND_activate_snapshot:
		s = find_snapshot(cmd->u.activate_snapshot.id);
		if (!s) {
			VG_(printf)("No snapshot %ld\n", cmd->u.activate_snapshot.id);
		} else {
			if (current_worker)
				kill_worker(current_worker);
			current_worker = activate_snapshot(s);
		}
		break;
	case COMMAND_run:
		if (!current_worker) {
			VG_(printf)("No current worker.\n");
		} else {
			run_worker(current_worker, cmd->u.run.nr);
		}
		break;
	case COMMAND_trace:
		if (!current_worker) {
			VG_(printf)("No current worker.\n");
		} else {
			trace_worker(current_worker, cmd->u.trace.nr);
		}
		break;
	case COMMAND_runm:
		if (!current_worker) {
			VG_(printf)("No current worker.\n");
		} else {
			run_m_worker(current_worker, cmd->u.runm.nr,
				     cmd->u.runm.thread);
		}
		break;
	}
}

static int
snapshot_command_loop(int fd)
{
	struct command_header ch;
	struct command_response resp;
	long child;
	int fds[2];
	int r;

	while (1) {
		safeish_read(fd, &ch, sizeof(ch));
		switch (ch.command) {
		case SNAPSHOT_KILL:
			resp.res = 0;
			safeish_write(fd, &resp, sizeof(resp));
			my__exit(0);

		case SNAPSHOT_ACTIVATE:
			VG_(printf)("Activating snapshot\n");
			r = socketpair(AF_UNIX, SOCK_STREAM, 0, fds);
			if (r < 0)
				VG_(tool_panic)((Char *)"error creating socket pair");
			child = my_fork();
			if (child < 0)
				VG_(tool_panic)((Char *)"forking worker");
			if (child == 0) {
				VG_(close)(fds[1]);
				VG_(close)(fd);
				return fds[0];
			}
			VG_(close)(fds[0]);
			resp.res = 0;
			safeish_write(fd, &resp, sizeof(resp));
			send_fd(fd, fds[1]);
			VG_(close)(fds[1]);
			break;

		default:
			VG_(tool_panic)((Char *)"bad snapshot command");
		}
	}
}

int
do_snapshot(int parent_fd)
{
	int fds[2];
	struct command_response resp;
	long child;
	int r;

	VG_(printf)("Snapshoting worker.\n");
	r = socketpair(AF_UNIX, SOCK_STREAM, 0, fds);
	if (r < 0)
		VG_(tool_panic)((Char *)"error creating socket pair");
	child = my_fork();
	if (child < 0)
		VG_(tool_panic)((Char *)"forking snapshot");
	if (child == 0) {
		VG_(close)(fds[1]);
		VG_(close)(parent_fd);
		return snapshot_command_loop(fds[0]);
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
	struct command cmd;
	int child;
	int fds[2];
	int r;

	r = socketpair(AF_UNIX, SOCK_STREAM, 0, fds);
	if (r < 0)
		VG_(tool_panic)((Char *)"Error creating socket pair");

	child = my_fork();
	if (child == 0) {
		VG_(close)(fds[1]);
		return snapshot_command_loop(fds[0]);
	}
	VG_(close)(fds[0]);

	root_snapshot = VG_(malloc)("root snapshot", sizeof(struct snapshot));
	VG_(memset)(root_snapshot, 0, sizeof(struct snapshot));
	root_snapshot->controlling_fd = fds[1];
	root_snapshot->id = ROOT_SNAPSHOT;

	while (1) {
		read_command(&cmd);
		run_command(&cmd);
	}
}
