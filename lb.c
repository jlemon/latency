#include <err.h>
#include <errno.h>
#include <stdio.h>
#include <fcntl.h>
#include <stdbool.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <locale.h>
#include <netdb.h>
#include <signal.h>
#include <poll.h>
#include <getopt.h>
#include <libgen.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/param.h>
#include <sys/mman.h>
#include <net/if.h>
#include <net/ethernet.h>
#include <netinet/in.h>
#include <netinet/udp.h>
#include <netinet/tcp.h>

#include <linux/ipv6.h>
#include <linux/if_packet.h>

#include "bpf/libbpf.h"
#include "bpf/xsk.h"
#include "bpf/bpf.h"

#include "liburing.h"

#include "glue_hdr.h"

#define MAX_SOCKS	4
#define BATCH_SIZE	64

#define err_with(rc, ...) do {						\
	errno = -rc;							\
	err(1, __VA_ARGS__);						\
} while (0)

struct umem {
	struct xsk_ring_prod fq;
	struct xsk_ring_cons cq;
	struct xsk_umem *lib_umem;
	void *buffer;
	unsigned *frame;
	int frame_count;
	int fq_refill;
};

struct xsk {
	struct xsk_ring_cons rx;
	struct xsk_ring_prod tx;
	struct umem *umem;
	struct xsk_socket *lib_xsk;
	int fd;

	unsigned long tx_queued;
	unsigned long tx_wakeup;

	unsigned long tx_npkts;
	unsigned long rx_npkts;
};

struct node {
	int family;
	int socktype;
	int protocol;
	struct ether_addr mac_addr;
	socklen_t addrlen;
	struct sockaddr_storage addr;
};

struct {
	bool stop;
	unsigned prog_id;
	int socktype;
	struct xsk *xsk[MAX_SOCKS];

	struct io_uring ring;
	int fd;
	char *buf;
} run;

enum transport_type {
	TRANSPORT_TCP,
	TRANSPORT_UDP,
	TRANSPORT_XDP,
	TRANSPORT_IOU,
};

enum rw_type {
	RW_BASIC,
	RW_MSG,
	RW_FIXED,
};

struct {
	const char *iface;
	bool poll;
	bool nonblock;
	bool use_wakeup;
	bool dual;
	bool end_summary;
	enum rw_type rw_api;
	enum transport_type transport;
	int ifindex;
	int frame_size;
	int num_frames;
	unsigned xdp_flags;
	unsigned bind_flags;
	unsigned mmap_flags;
	unsigned umem_flags;
	int num_xsks;
	int queue;
	int timeout;
	int port;
	int iou_entries;
} opt = {
	.iface = "eth0",
	.nonblock = true,
	.use_wakeup = true,
	.poll = false,
	.transport = TRANSPORT_TCP,
	.num_frames = (16 * 1024),
	.frame_size = XSK_UMEM__DEFAULT_FRAME_SIZE,
	.num_xsks = 1,
	.timeout = 1000,
	.queue = 32,
	.port = 7777,
	.iou_entries = 64,
};

static struct node self; 
static struct node peer; 

static const char *transport_name[] = {
	[TRANSPORT_TCP] = "TCP",
	[TRANSPORT_UDP] = "UDP",
	[TRANSPORT_XDP] = "XDP",
	[TRANSPORT_IOU] = "IOU",
};

static void statistics(void);
static void progress(void);

static void
handle_signal(int sig)
{
	run.stop = true;
}

static void
set_nonblocking(int fd, bool on)
{
	int rc, flag;

	flag = fcntl(fd, F_GETFL);
	if (flag == -1)
		err(1, "fcntl(F_GETFL)");

	if (on)
		flag |= O_NONBLOCK;
	else
		flag &= ~O_NONBLOCK;

	rc = fcntl(fd, F_SETFL, flag);
	if (rc == -1)
		err(1, "fcntl(F_SETFL)");
}

void
show(int family, struct sockaddr *addr)
{
	char host[NI_MAXHOST];
	int rc;

	rc = getnameinfo(addr,
	    (family == AF_INET) ? sizeof(struct sockaddr_in) :
				  sizeof(struct sockaddr_in6),
	    host, NI_MAXHOST, NULL, 0, NI_NUMERICHOST);
	if (rc != 0)
		errx(1, "getnameinfo: %s", gai_strerror(rc));

	printf("hostname: %s\n", host);
}

static inline bool
fd_read_ready(int fd)
{
	struct pollfd pfd = {
		.fd = fd,
		.events = POLLIN,
	};
	int n;

	if (!opt.poll)
		return true;
	
	for (;;) {
		n = poll(&pfd, 1, opt.timeout);
		if (n == 1)
			return true;
		if (n == -1) {
			run.stop = true;
			return false;
		}
	}
}


/*---------------------------------------------------------------------------*/
static void
normalize_tcp_link(int fd)
{
	int rc;
	int one = 1;
	struct timeval tv = { };

	set_nonblocking(fd, opt.nonblock);

	rc = setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
	if (rc == -1)
		err(1, "setsockopt(TCP_NODELAY)");

	rc = setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	if (rc == -1)
		err(1, "setsockopt(SO_RCVTIMEO)");

	rc = setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
	if (rc == -1)
		err(1, "setsockopt(SO_SNDTIMEO)");
}

static int
tcp_wait_connect(int server)
{
	struct sockaddr_storage ss;
	socklen_t addrlen;
	int fd;

	fd = accept(server, (struct sockaddr *)&ss, &addrlen);
	if (fd == -1)
		err(1, "accept");

	normalize_tcp_link(fd);

	return fd;
}

static int
tcp_server_setup(struct node *node)
{
	int fd, rc;
	int one = 1;

	fd = socket(node->family, node->socktype, node->protocol);
	if (fd == -1)
		err(1, "socket");

	rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	if (rc == -1)
		err(1, "setsockopt(REUSEADDR)");

	rc = bind(fd, (struct sockaddr *)&node->addr, node->addrlen);
	if (rc == -1)
		err(1, "bind");

	rc = listen(fd, 1);
	if (rc == -1)
		err(1, "listen");

	return fd;
}

static void
tcp_server_pingpong(int c_send, int c_recv)
{
	char buf[8];
	int n;

	while (!run.stop) {
		n = read(c_recv, buf, 1);
		if (n == 1) {
			n = write(c_send, buf, 1);
			if (n != 1)
				break;
			continue;
		}
		if (n == 0)
			break;
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			continue;
		break;
	}
}

static void
tcp_server(void)
{
	int server, c_send, c_recv;

	server = tcp_server_setup(&self);
	while (!run.stop) {
		c_send = c_recv = tcp_wait_connect(server);
		if (opt.dual)
			c_send = tcp_wait_connect(server);
		printf("new connection, [%d,%d]\n", c_recv, c_send);
		tcp_server_pingpong(c_send, c_recv);
		close(c_send);
		if (opt.dual)
			close(c_recv);
		printf("client done\n");
	}
}

static int
tcp_client_setup(struct node *node)
{
	int fd, rc;
	int one = 1;

	fd = socket(node->family, node->socktype, node->protocol);
	if (fd == -1)
		err(1, "socket");

	rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	if (rc == -1)
		err(1, "setsockopt(REUSEADDR)");

	rc = connect(fd, (struct sockaddr *)&node->addr, node->addrlen);
	if (rc == -1)
		err(1, "connect");

	normalize_tcp_link(fd);

	return fd;
}

static void
tcp_client_pingpong(int c_send, int c_recv)
{
	unsigned long start;
	char buf[8];
	int n;

	while (!run.stop) {
		start = nsec();
		n = write(c_send, buf, 1);
		if (n != 1)
			break;
		while (!run.stop) {
			if (!fd_read_ready(c_recv))
				continue;
			n = read(c_recv, buf, 1);
			if (n == 1) {
				if (!stat_add(elapsed(start)))
					run.stop = true;
				progress();
				break;
			}
			if (errno == EAGAIN || errno == EWOULDBLOCK)
				continue;
			run.stop = true;
		}
	}
}

static void
tcp_client(void)
{
	int c_send, c_recv;

	c_send = c_recv = tcp_client_setup(&peer);
	if (opt.dual)
		c_recv = tcp_client_setup(&peer);
	tcp_client_pingpong(c_send, c_recv);
	close(c_send);
	if (opt.dual)
		close(c_recv);
}
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
static int
udp_server_setup(struct node *node)
{
	int fd, rc;
	int one = 1;

	fd = socket(node->family, node->socktype, node->protocol);
	if (fd == -1)
		err(1, "socket");

	rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	if (rc == -1)
		err(1, "setsockopt(REUSEADDR)");

	rc = bind(fd, (struct sockaddr *)&node->addr, node->addrlen);
	if (rc == -1)
		err(1, "bind");

	return fd;
}

static void
udp_server_pingpong(int fd)
{
	char buf[8];
	int n;

	while (!run.stop) {
		peer.addrlen = sizeof(peer.addr);
		n = recvfrom(fd, buf, 1, 0,
		    (struct sockaddr *)&peer.addr, &peer.addrlen);
		if (n == 1) {
			n = sendto(fd, buf, 1, 0,
			    (struct sockaddr *)&peer.addr, peer.addrlen);
			if (n != 1) {
				err(1, "sendto");
				break;
			}
			continue;
		}
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			continue;
		break;
	}
}

static void
udp_server(void)
{
	int local;

	local = udp_server_setup(&self);
	udp_server_pingpong(local);
}

static int
udp_client_setup(struct node *node)
{
	int fd, rc;
	int one = 1;

	fd = socket(node->family, node->socktype, node->protocol);
	if (fd == -1)
		err(1, "socket");

	rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	if (rc == -1)
		err(1, "setsockopt(REUSEADDR)");

	rc = connect(fd, (struct sockaddr *)&node->addr, node->addrlen);
	if (rc == -1)
		err(1, "connect");

	return fd;
}

static void
udp_client_pingpong(int fd)
{
	unsigned long start;
	char buf[8];
	int n;

/* running in busypoll mode (non-blocking) results in packet drops & stalls */

	while (!run.stop) {
		start = nsec();
		n = send(fd, buf, 1, 0);
		if (n != 1)
			break;
		while (!run.stop) {
			if (!fd_read_ready(fd))
				continue;
			n = recv(fd, buf, 1, 0);
			if (n == 1) {
				if (!stat_add(elapsed(start)))
					run.stop = true;
				progress();
				break;
			}
			if (errno == EAGAIN || errno == EWOULDBLOCK)
				continue;
			run.stop = true;
		}
	}
}

static void
udp_client(void)
{
	int fd;

	fd = udp_client_setup(&peer);
	udp_client_pingpong(fd);
	close(fd);
}
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* IO_URING */

static void
iou_setup(void)
{
	unsigned flags = 0;
	struct iovec iov;
	int fd, rc, size;

#if 0
	/* This is incompatible with IORING_OP_POLL */
	if (opt.poll)
		flags |= IORING_SETUP_IOPOLL;
#endif

#if 0
	flags |= IORING_SETUP_SQPOLL;	/* submission polling kernel thread */
	flags |= IORING_SETUP_SQ_AFF;	/* bind poll thread to specific cpu */
#endif

	/* simplified api that only sets flags. */
	fd = io_uring_queue_init(opt.iou_entries, &run.ring, flags);
	if (fd == -1)
		err(1, "iou_queue_init");
	run.fd = fd;

	if (opt.rw_api == RW_FIXED) {
		size = 4096;
		run.buf = mmap(NULL, size, PROT_READ|PROT_WRITE,
		    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		if (run.buf == MAP_FAILED)
			err(1, "mmap");
		iov.iov_base = run.buf;
		iov.iov_len = size;
		rc = io_uring_register_buffers(&run.ring, &iov, 1);
		if (rc == -1)
			err(1, "io_uring_register_buffers");
	}
}

static int
iou_wait_recv(int fd, char *buf, unsigned len)
{
	struct io_uring *ring = &run.ring;
        struct io_uring_sqe *sqe;
        struct io_uring_cqe *cqe;
	struct iovec iov = {
		.iov_base = buf,
		.iov_len = len,
	};
	struct msghdr msg = {
		.msg_iov = &iov,
		.msg_iovlen = 1,
		.msg_namelen = peer.addrlen,
	};
	int count, head, nr, rc;

retry:
	nr = 1;
	if (opt.poll) {
		sqe = io_uring_get_sqe(ring);
		io_uring_prep_poll_add(sqe, fd, POLLIN);
		io_uring_sqe_set_flags(sqe, IOSQE_IO_LINK);
		io_uring_sqe_set_data(sqe, (void *)1);
		nr++;
	}

        sqe = io_uring_get_sqe(ring);
	if (opt.rw_api == RW_BASIC)
		io_uring_prep_readv(sqe, fd, &iov, 1, 0);
	else if (opt.rw_api == RW_MSG)
		io_uring_prep_recvmsg(sqe, fd, &msg, 0);
	else
		io_uring_prep_read_fixed(sqe, fd, buf, 1, 0, 0);

        rc = io_uring_submit_and_wait(ring, nr);
        if (rc <= 0)
		err(1, "recv submit: %d", rc);
	io_uring_for_each_cqe(ring, head, cqe) {
		if (io_uring_cqe_get_data(cqe) == (void *)1) {
			if (cqe->res < 0)
				err_with(cqe->res, "cqe(POLLIN) failed");
			if ((cqe->res & POLLIN) == 0)
				errx(1, "linked POLL returns 0x%x", cqe->res);
			continue;
		}
		count = cqe->res;
	}
	io_uring_cq_advance(ring, nr);
	if (count < 0) {
		if (!opt.poll)
			goto retry;
		statistics();	
		err_with(count, "cqe(READV) failed");
	}
	return count;
}

void
iou_send(int fd, char *buf, unsigned len)
{
	struct io_uring *ring = &run.ring;
        struct io_uring_sqe *sqe;
        struct io_uring_cqe *cqe;
	struct iovec iov = {
		.iov_base = buf,
		.iov_len = len,
	};
	int nr, rc;

	nr = 1;
#if 0
	if (opt.poll) {
		sqe = io_uring_get_sqe(ring);
		io_uring_prep_poll_add(sqe, fd, POLLOUT);
		io_uring_sqe_set_flags(sqe, IOSQE_IO_LINK);
		nr++;
	}
#endif

        sqe = io_uring_get_sqe(ring);
	io_uring_prep_writev(sqe, fd, &iov, 1, 0);
	io_uring_sqe_set_data(sqe, 0xdead);

        rc = io_uring_submit_and_wait(ring, nr);
        if (rc <= 0)
		err(1, "send submit: %d", rc);
/* XXX io_uring_for_each_cqe(ring, int head, cqe) {  */
	rc = io_uring_wait_cqe_nr(ring, &cqe, nr);
	if (rc < 0)
		err_with(rc, "iou_send, wait_cqe");
	if (opt.poll && nr > 1) {
		if (cqe->res < 0)
			err_with(cqe->res, "cqe(POLLOUT) failed");
		if ((cqe->res & POLLOUT) == 0)
			errx(1, "linked POLLOUT returns 0x%x", cqe->res);
		cqe++;
	}
	if (cqe->res < 0)
		err_with(cqe->res, "iou_send, cqe failed");
	if (cqe->res != 1)
		errx(1, "short write, res %d", cqe->res);
	io_uring_cq_advance(ring, nr);
}

static void
iou_server_pingpong(int c_send, int c_recv)
{
	int n;
	char buf[8];

	while (!run.stop) {
		n = iou_wait_recv(c_recv, buf, 1); //sizeof(buf));
		if (n == 0)
			break;
		iou_send(c_send, buf, n);
	}
}

static void
iou_server(void)
{
	int server, c_send, c_recv;

	iou_setup();
	server = tcp_server_setup(&self);
	while (!run.stop) {
		c_send = c_recv = tcp_wait_connect(server);
		if (opt.dual)
			c_send = tcp_wait_connect(server);
		printf("new connection, [%d,%d]\n", c_recv, c_send);
		iou_server_pingpong(c_send, c_recv);
		close(c_send);
		if (opt.dual)
			close(c_recv);
		printf("client done\n");
	}
}

static void
iou_client_pingpong(int c_send, int c_recv)
{
	unsigned long start;
	char buffer[8], *buf;
	int n;

	buf = buffer;
	if (opt.rw_api == RW_FIXED)
		buf = run.buf;

	while (!run.stop) {
		start = nsec();
		iou_send(c_send, buf, 1);
		n = iou_wait_recv(c_recv, buf, 1);
		if (n == 0)
			errx(1, "wait_recv returned 0");
		if (!stat_add(elapsed(start)))
			run.stop = true;
		progress();
	}
}

static void
iou_client(void)
{
	int c_send, c_recv;

	iou_setup();
	c_send = c_recv = tcp_client_setup(&peer);
	if (opt.dual)
		c_recv = tcp_client_setup(&peer);
	iou_client_pingpong(c_send, c_recv);
	close(c_send);
	if (opt.dual)
		close(c_recv);
}
/*---------------------------------------------------------------------------*/
/* AF_XDP */

static u64
umem_pop_frame(struct umem *umem)
{
	if (umem->frame_count == 0)
		errx(1, "out of frames");
	return umem->frame[--umem->frame_count];
}

static void
umem_push_frame(struct umem *umem, u64 addr)
{
	if (umem->frame_count == opt.num_frames)
		errx(1, "too many frames");
	umem->frame[umem->frame_count++] = addr;
}

static void
populate_fill_ring(struct umem *umem, int count)
{
	int rc, i;
	u64 addr;
	u32 idx;

	rc = xsk_ring_prod__reserve(&umem->fq, count, &idx);
	if (rc != count)
		err_with(rc, "ring_prod_reserve");

	for (i = 0; i < count; i++) {
		addr = umem_pop_frame(umem);
		*xsk_ring_prod__fill_addr(&umem->fq, idx++) = addr;
	}
	xsk_ring_prod__submit(&umem->fq, count);
printf("reload fill ring with %d, left %d\n", count, umem->frame_count);
}

static struct umem *
configure_umem(void *buffer, u64 size)
{
	struct xsk_umem_config cfg = {
		.fill_size = XSK_RING_PROD__DEFAULT_NUM_DESCS,
		.comp_size = XSK_RING_CONS__DEFAULT_NUM_DESCS,
		.frame_size = opt.frame_size,
		.frame_headroom = XSK_UMEM__DEFAULT_FRAME_HEADROOM,
		.flags = opt.umem_flags
	};
	struct umem *umem;
	int i, rc;

	umem = calloc(1, sizeof(*umem));
	if (!umem)
		err(1, "calloc");

	rc = xsk_umem__create(&umem->lib_umem, buffer, size,
	    &umem->fq, &umem->cq, &cfg);
	if (rc)
		err_with(rc, "xsk_umem__create");
	umem->buffer = buffer;
	umem->fq_refill = cfg.fill_size / 2;

	umem->frame = calloc(opt.num_frames, sizeof(unsigned));
	for (i = 0; i < opt.num_frames; i++)
		umem->frame[i] = i * opt.frame_size;
	umem->frame_count = opt.num_frames;

	if (cfg.fill_size)
		populate_fill_ring(umem, cfg.fill_size);

	return umem;
}

static struct xsk *
configure_socket(struct umem *umem, int queue, bool rx, bool tx)
{
	struct xsk_socket_config cfg = {
		.rx_size = XSK_RING_CONS__DEFAULT_NUM_DESCS,
		.tx_size = XSK_RING_PROD__DEFAULT_NUM_DESCS,
		.libbpf_flags = 0,
		.xdp_flags = opt.xdp_flags,
		.bind_flags = opt.bind_flags,
	};
	struct xsk_ring_cons *rxr;
	struct xsk_ring_prod *txr;
	struct xsk *xsk;
	int rc;

	xsk = calloc(1, sizeof(*xsk));
	if (!xsk)
		err(1, "calloc");

	rxr = rx ? &xsk->rx : NULL;
	txr = tx ? &xsk->tx : NULL;
	rc = xsk_socket__create(&xsk->lib_xsk, opt.iface, queue,
			umem->lib_umem, &xsk->rx, &xsk->tx, &cfg);
	if (rc)
		err_with(rc, "xsk_socket__create");

	xsk->umem = umem;
	xsk->fd = xsk_socket__fd(xsk->lib_xsk);

	rc = bpf_get_link_xdp_id(opt.ifindex, &run.prog_id, opt.xdp_flags);
	if (rc)
		err_with(rc, "bpf_get_link_xdp_id");

	return xsk;
}

static void
xdp_setup(void)
{
	struct umem *umem;
	void *buffer;
	size_t size;
	int i;

	size = opt.num_frames * opt.frame_size;

	/* Reserve memory for the umem. Use hugepages if unaligned chunk mode */
	buffer = mmap(NULL, size, PROT_READ | PROT_WRITE,
		    MAP_PRIVATE | MAP_ANONYMOUS | opt.mmap_flags, -1, 0);
	if (buffer == MAP_FAILED)
		err(1, "mmap");

	/* Create sockets... */
	umem = configure_umem(buffer, size);
	for (i = 0; i < opt.num_xsks; i++)
		run.xsk[i] = configure_socket(umem, opt.queue + i, true, true);
}

static inline void
wakeup_driver(int fd)
{
	struct pollfd pfd;

	pfd.fd = fd;
	pfd.events = POLLIN;
	poll(&pfd, 1, 0);
}

static void
kick_tx(struct xsk *xsk)
{

	/* don't wake up if already done */
	if (xsk->tx_queued == xsk->tx_wakeup)
		return;

	wakeup_driver(xsk->fd);
	xsk->tx_wakeup = xsk->tx_queued;
}

#if 0
set rx need wakeup - on FQ. why on fq? 
 since this is set only on 'allocation error', aka out of fq space.
 needs RX wakeup is a signal that FQ was empty, and driver is idle.
#endif

#if 0
static void
tx_cq_to_fq(struct xsk *xsk, struct pollfd *pfd)
{
	struct umem *umem = xsk->umem;
	u32 idx_cq = 0, idx_fq = 0;
	unsigned int rcvd, ret;
	size_t ndescs;

	if (!xsk->outstanding_tx)
		return;

	if (!opt.use_wakeup || xsk_ring_prod__needs_wakeup(&xsk->tx))
		kick_tx(xsk);

	ndescs = (xsk->outstanding_tx > BATCH_SIZE) ? BATCH_SIZE :
		xsk->outstanding_tx;

	/* re-add completed Tx buffers */
	rcvd = xsk_ring_cons__peek(&umem->cq, ndescs, &idx_cq);
	if (rcvd > 0) {
		unsigned int i;

		ret = xsk_ring_prod__reserve(&umem->fq, rcvd, &idx_fq);
		while (ret != rcvd) {
printf("could not reserve space in FQ\n");
			if (ret < 0)
				err_with(ret, "FQ prod reserve");
			if (xsk_ring_prod__needs_wakeup(&umem->fq)) {
				ret = poll(pfd, 1, 0);
			}
			ret = xsk_ring_prod__reserve(&umem->fq, rcvd, &idx_fq);
		}

		for (i = 0; i < rcvd; i++)
			*xsk_ring_prod__fill_addr(&umem->fq, idx_fq++) =
				*xsk_ring_cons__comp_addr(&umem->cq, idx_cq++);

		xsk_ring_prod__submit(&xsk->umem->fq, rcvd);
		xsk_ring_cons__release(&xsk->umem->cq, rcvd);
		xsk->outstanding_tx -= rcvd;
		xsk->tx_npkts += rcvd;
	}
}
#endif

/* UDP ping from kerneltest001.11.lla2 to kerneltest002.11.lla2:7777 */

static uint8_t pkt_c2s[] = {
	0x24, 0x8a, 0x07, 0x8b, 0x00, 0xce,	/* dst mac */
	0x24, 0x8a, 0x07, 0x8b, 0x00, 0x28,	/* src mac */
	0x86, 0xdd,				/* ethernet */

	/* ip6 hdr */
	0x60, 0x00,
	0x00, 0x00, 0x00, 0x09, 0x11, 0x7f,

	/* ip6 src addr */
	0x24, 0x01, 0xdb, 0x00, 0x30, 0x20, 0xb2, 0x37,
	0xfa, 0xce, 0x00, 0x00, 0x00, 0x6d, 0x00, 0x00,

	/* ip6 dst addr */
	0x24, 0x01, 0xdb, 0x00, 0x30, 0x20, 0xb2, 0x37,
	0xfa, 0xce, 0x00, 0x00, 0x00, 0x36, 0x00, 0x00,

	/* udp */
	0xa9, 0xc9, 0x1e, 0x61, 0x00, 0x09, 0x39, 0xbd,

	/* payload */
	0x45
};

/* UDP pong from kerneltest002.11.lla2:7777 to kerneltest002.11.lla2 */

static uint8_t pkt_s2c[] = {
	0x24, 0x8a, 0x07, 0x8b, 0x00, 0x28,	/* src mac */
	0x24, 0x8a, 0x07, 0x8b, 0x00, 0xce,	/* dst mac */
	0x86, 0xdd,				/* ethernet */

	/* ip6 hdr */
	0x60, 0x00,
	0x00, 0x00, 0x00, 0x09, 0x11, 0x7f,

	/* ip6 src addr */
	0x24, 0x01, 0xdb, 0x00, 0x30, 0x20, 0xb2, 0x37,
	0xfa, 0xce, 0x00, 0x00, 0x00, 0x36, 0x00, 0x00,

	/* ip6 dst addr */
	0x24, 0x01, 0xdb, 0x00, 0x30, 0x20, 0xb2, 0x37,
	0xfa, 0xce, 0x00, 0x00, 0x00, 0x6d, 0x00, 0x00,

	/* udp */
	0x1e, 0x61, 0xa9, 0xc9, 0x00, 0x09, 0xb9, 0x0e,

	/* payload */
	0x45
};

static int
xdp_pingpong(char *pkt)
{
	memcpy(pkt, pkt_s2c, sizeof(pkt_s2c));
	return sizeof(pkt_s2c);
}

#if 0
for the mlx5 driver, when there is an alloction error (fq is depleted)
then it sets 'needs wakeup' on the FQ (and possibly idles the driver).
userspace needs to replenish the FQ, then poke the driver.

Here, driver waits for next scheduled irq/napi before doing more 
allocations, so user space could spin/compete with driver.
#endif

/*
 * Fill queue may need attention.  Provide more buffers and notify the driver.
 * Needs some type of hysteresis here so the driver has a chance to clear the
 * need wakeup flag.
 */
static void
check_xsk_fq(struct xsk *xsk)
{
	struct umem *umem = xsk->umem;
	int count;

	if (!xsk_ring_prod__needs_wakeup(&umem->fq))
		return;

	count = xsk_prod_nb_free(&umem->fq, umem->fq_refill);

	if (count < umem->fq_refill)
		return;

	count = MIN(count, umem->frame_count);

	populate_fill_ring(umem, count);

	wakeup_driver(xsk->fd);
}

static void
check_xsk_cq(struct xsk *xsk)
{
	struct umem *umem = xsk->umem;
	int count, i;
	u32 idx = 0;
	u64 addr;

	if (xsk->tx_queued == xsk->tx_npkts)
		return;

	if (!opt.use_wakeup || xsk_ring_prod__needs_wakeup(&xsk->tx))
		kick_tx(xsk);

	count = xsk_ring_cons__peek(&umem->cq, BATCH_SIZE, &idx);
	if (!count)
		return;

	for (i = 0; i < count; i++) {
		addr = *xsk_ring_cons__comp_addr(&umem->cq, idx++);
		umem_push_frame(umem, addr);
	}
	xsk_ring_cons__release(&xsk->umem->cq, count);

	xsk->tx_npkts += count;
}


static void
xdp_server_reflect(struct xsk *xsk, struct pollfd *pfd)
{
	unsigned int rcvd, i;
	u32 idx_rx = 0, idx_tx = 0;
	int ret;

	rcvd = xsk_ring_cons__peek(&xsk->rx, BATCH_SIZE, &idx_rx);
	if (!rcvd) {
		check_xsk_fq(xsk);
		return;
	}
//printf("--- received packet\n");

	ret = xsk_ring_prod__reserve(&xsk->tx, rcvd, &idx_tx);
	while (ret != rcvd) {
		if (ret < 0)
			err_with(ret, "TX prod reserve");
		if (xsk_ring_prod__needs_wakeup(&xsk->tx))
			kick_tx(xsk);
		ret = xsk_ring_prod__reserve(&xsk->tx, rcvd, &idx_tx);
	}

	for (i = 0; i < rcvd; i++) {
		const struct xdp_desc *rx_desc;
		struct xdp_desc *tx_desc;
		u64 addr, base;
		char *pkt;
		u32 len;

		rx_desc = xsk_ring_cons__rx_desc(&xsk->rx, idx_rx++);
		base = xsk_umem__extract_addr(rx_desc->addr);
		addr = xsk_umem__add_offset_to_addr(rx_desc->addr);
		len = rx_desc->len;

		pkt = xsk_umem__get_data(xsk->umem->buffer, addr);
		len = xdp_pingpong(pkt);

		tx_desc = xsk_ring_prod__tx_desc(&xsk->tx, idx_tx++);
		tx_desc->addr = base;
		tx_desc->len = len;
	}

	xsk_ring_prod__submit(&xsk->tx, rcvd);
	xsk_ring_cons__release(&xsk->rx, rcvd);

	xsk->rx_npkts += rcvd;
	xsk->tx_queued += rcvd;
}

static void
xdp_server(void)
{
	struct pollfd pfd = {};
	int rc;

	xdp_setup();

	pfd.fd = run.xsk[0]->fd;
	pfd.events = POLLIN;

	while (!run.stop) {
		if (opt.poll) {
			rc = poll(&pfd, 1, opt.timeout);
			if (rc == -1)
				err(1, "poll");
printf("poll result %d	%x\n", rc, pfd.revents);
		}
		xdp_server_reflect(run.xsk[0], &pfd);
		check_xsk_cq(run.xsk[0]);
	}
}

static void
xdp_client_recv(struct xsk *xsk, struct pollfd *pfd)
{
	unsigned int rcvd, i;
	u32 idx_rx = 0, idx_fq = 0;
	int ret;

	rcvd = xsk_ring_cons__peek(&xsk->rx, BATCH_SIZE, &idx_rx);
	if (!rcvd) {
//		check_xsk_fq(xsk);
		return;
	}

	ret = xsk_ring_prod__reserve(&xsk->umem->fq, rcvd, &idx_fq);
	while (ret != rcvd) {
		if (ret < 0)
			err_with(ret, "FQ prod reserve");
		if (xsk_ring_prod__needs_wakeup(&xsk->umem->fq))
			ret = poll(pfd, 1, opt.timeout);
		ret = xsk_ring_prod__reserve(&xsk->umem->fq, rcvd, &idx_fq);
	}

	for (i = 0; i < rcvd; i++) {
		u64 addr = xsk_ring_cons__rx_desc(&xsk->rx, idx_rx)->addr;
		u64 orig = xsk_umem__extract_addr(addr);

		*xsk_ring_prod__fill_addr(&xsk->umem->fq, idx_fq++) = orig;
	}

	xsk_ring_prod__submit(&xsk->umem->fq, rcvd);
	xsk_ring_cons__release(&xsk->rx, rcvd);
	xsk->rx_npkts += rcvd;
}

unsigned
fill_eth(struct node *dst, struct node *src, void *packet)
{
	struct ether_header *eth = packet;

	memcpy(&eth->ether_dhost, &dst->mac_addr, sizeof(eth->ether_dhost));
	memcpy(&eth->ether_shost, &src->mac_addr, sizeof(eth->ether_shost));
	eth->ether_type = ETHERTYPE_IPV6;

	return sizeof(*eth);
}

unsigned
fill_ip6(struct node *dst, struct node *src, void *packet, int payload_len)
{
	struct ipv6hdr *ip6 = packet;
	struct sockaddr_in6 *self_sin6 = (struct sockaddr_in6 *)&self.addr;
	struct sockaddr_in6 *peer_sin6 = (struct sockaddr_in6 *)&peer.addr;

	ip6->version = 6;
	ip6->priority = 0;
	memset(ip6->flow_lbl, 0, sizeof(ip6->flow_lbl));
	ip6->payload_len = htons(ntohs(payload_len) + sizeof(*ip6));
	ip6->nexthdr = IPPROTO_IPV6;
	ip6->hop_limit = 8;
	memcpy(&ip6->saddr, &self_sin6->sin6_addr, sizeof(ip6->saddr));
	memcpy(&ip6->daddr, &peer_sin6->sin6_addr, sizeof(ip6->daddr));

	return sizeof(*ip6);
}

unsigned
fill_udp(struct node *dst, struct node *src, void *packet, int payload_len)
{
	struct udphdr *udp = packet;
	struct sockaddr_in6 *self_sin6 = (struct sockaddr_in6 *)&self.addr;
	struct sockaddr_in6 *peer_sin6 = (struct sockaddr_in6 *)&peer.addr;

	udp->source = self_sin6->sin6_port;
	udp->dest = peer_sin6->sin6_port;
	udp->len = payload_len;
	udp->check = 0;

	return sizeof(*udp);
}

int
build_packet(struct node *dst, struct node *src, uint8_t *packet)
{
	unsigned len;

	len = fill_eth(dst, src, packet);
	len += fill_ip6(dst, src, packet + len, 1);
	len += fill_udp(dst, src, packet + len, 1);

	packet[len] = 'X';

	return len + 1;
}

static int
generate_ping(void *pkt)
{
//	return build_packet(&peer, &self, pkt);

	memcpy(pkt, pkt_c2s, sizeof(pkt_c2s));
	return sizeof(pkt_c2s);
}

static void
xdp_client_send_pkt(struct xsk *xsk, struct pollfd *pfd)
{
	struct xdp_desc *desc;
	char *pkt;
	u64 addr;
	u32 idx;
	int len;

	if (xsk_ring_prod__reserve(&xsk->tx, 1, &idx) != 1)
		errx(1, "TX prod reserve");

//printf(" ---- sending packet \n");
	addr = umem_pop_frame(xsk->umem);
	pkt = xsk_umem__get_data(xsk->umem->buffer, addr);

	len = generate_ping(pkt);

	desc = xsk_ring_prod__tx_desc(&xsk->tx, idx);
	desc->addr = addr;
	desc->len = len;

	xsk_ring_prod__submit(&xsk->tx, 1);
	xsk->tx_queued++;
}

static bool
xdp_client_wait_resp(struct xsk *xsk, struct pollfd *pfd)
{
	unsigned long rcvd;

	rcvd = xsk->rx_npkts;

	while (!run.stop) {
		check_xsk_cq(xsk);
		xdp_client_recv(xsk, pfd);
		if (xsk->rx_npkts != rcvd)
			return true;
	}
	return false;
}

static void
xdp_client(void)
{
	struct pollfd pfd = {};
	unsigned long start;
	struct xsk *xsk;

	xdp_setup();

	xsk = run.xsk[0];
	pfd.fd = xsk->fd;
	pfd.events = POLLOUT | POLLIN;

	while (!run.stop) {
		start = nsec();
		xdp_client_send_pkt(xsk, &pfd);
		if (xdp_client_wait_resp(xsk, &pfd)) {
			if (!stat_add(elapsed(start)))
				run.stop = true;
			progress();
		}
	}
}

/*---------------------------------------------------------------------------*/

static bool
name2addr(const char *name, struct node *node, bool local)
{
	struct addrinfo hints, *result, *ai;
	int s, rc;

	memset(&hints, 0, sizeof(struct addrinfo));
	hints.ai_family = node->family;
	hints.ai_socktype = node->socktype;
	node->addrlen = 0;

	rc = getaddrinfo(name, NULL, &hints, &result);
	if (rc != 0)
		errx(1, "getaddrinfo: %s", gai_strerror(rc));

	for (ai = result; ai != NULL; ai = ai->ai_next) {
		if (!local)
			break;

		s = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
		if (s == -1)
			continue;

		rc = bind(s, ai->ai_addr, ai->ai_addrlen);
		close(s);

		if (rc == 0)
			break;
	}

	if (ai != NULL) {
		node->addrlen = ai->ai_addrlen;
		node->protocol = ai->ai_protocol;
		memcpy(&node->addr, ai->ai_addr, ai->ai_addrlen);
	}

	freeaddrinfo(result);

	return node->addrlen != 0;
}

static void
init(const char *peername)
{
	struct sockaddr_in6 *sin6;
	char name[HOST_NAME_MAX];

	if (gethostname(name, sizeof(name)) == -1)
		err(1, "gethostname");

	self.family = AF_INET6;
	self.socktype = run.socktype;
	if (!name2addr(name, &self, true))
		errx(1, "could not get IP of %s", name);

	sin6 = (struct sockaddr_in6 *)&self.addr;
	sin6->sin6_port = htons(opt.port);

	if (peername == NULL)
		return;

	peer.family = AF_INET6;
	peer.socktype = run.socktype;
	if (!name2addr(peername, &peer, false))
		errx(1, "could not get IP of %s", peername);

	sin6 = (struct sockaddr_in6 *)&peer.addr;
	sin6->sin6_port = htons(opt.port);
}

static void
cleanup(void)
{
}

static void
initialize(void)
{
	struct rlimit r = {RLIM_INFINITY, RLIM_INFINITY};
	struct sigaction sa = {
		.sa_handler = handle_signal,
	};
	int rc;

	rc = setrlimit(RLIMIT_MEMLOCK, &r);
	if (rc)
		err(1, "setrlimit(RLIMIT_MEMLOCK)");

	atexit(cleanup);

	sigaction(SIGINT, &sa, NULL);
	sigaction(SIGTERM, &sa, NULL);
	sigaction(SIGABRT, &sa, NULL);

#if 0
	/* Sigh, Linux automatically sets SA_RESTART */
	signal(SIGINT, handle_signal);
	signal(SIGTERM, handle_signal);
	signal(SIGABRT, handle_signal);
#endif

	setlocale(LC_ALL, "");
}

static void
statistics(void)
{
	char *scale_str = "(us)";
	static int last = 0;
	int scale = 1000;
	int count = stat_count();

	if (count == last)
		return;

	if (last == 0) {
		printf("\n");
		printf("%-10.10s %4s%4s %4s%4s %4s%4s %4s%4s %4s%4s %4s%4s %9s\n",
		    "test",
		    "min", scale_str,
		    "p25", scale_str,
		    "p50", scale_str,
		    "p90", scale_str,
		    "p99", scale_str,
		    "max", scale_str,
		    "samples");
	}
	printf("%-10.10s %8d %8d %8d %8d %8d %8d %8d\n",
	    transport_name[opt.transport],
	    stat_pct(0.0) / scale,
	    stat_pct(25.0) / scale,
	    stat_pct(50.0) / scale,
	    stat_pct(90.0) / scale,
	    stat_pct(99.0) / scale,
	    stat_pct(100.0) / scale,
	    count);

	last = count;
}

static void
progress(void)
{
	int count;

	if (opt.end_summary)
		return;

	count = stat_count();
	if ((count % 1000) == 0)
		statistics();
}

#if 0
test modes:
 - pingpong = one node sends out response, wait for reply.
 - barrier_all_to_all: each node pings all, waits for pong response.
 - barrier_all_to_one: !root sends out ping, waits for pong
     - root collects all pings, sends out pong.

pingpong and all2all are fairly close.	pingpong is slower.
 all_to_one is faster - presumably piggybacking responses?

implementations:
 - tcp, blocking sockets
 - tcp, busy loop
 - tcp, poll

 - udp

 - af_xdp

#endif

static struct option options[] = {
	{"block", no_argument, 0, 'b'},
	{"tcp", no_argument, 0, 't'},
	{"udp", no_argument, 0, 'u'},
	{"xdp", no_argument, 0, 'x'},
	{"iou", no_argument, 0, 'o'},
	{"poll", no_argument, 0, 'p'},
	{"port", required_argument, 0, 'P'},
	{"dual", no_argument, 0, '2'},
	{"end", no_argument, 0, 'e'},
	{"msg", no_argument, 0, 'm'},
	{"fixed", no_argument, 0, 'f'},
#if 0
	{"l2fwd", no_argument, 0, 'l'},
	{"interface", required_argument, 0, 'i'},
	{"queue", required_argument, 0, 'q'},
	{"poll", no_argument, 0, 'p'},
	{"xdp-skb", no_argument, 0, 'S'},
	{"xdp-native", no_argument, 0, 'N'},
	{"interval", required_argument, 0, 'n'},
	{"thread", required_argument, 0, 't'},
	{"zero-copy", no_argument, 0, 'z'},
	{"copy", no_argument, 0, 'c'},
	{"frame-size", required_argument, 0, 'f'},
#endif
	{0, 0, 0, 0}
};

#define OPTSTR "2befmopP:tux"

static void
usage(const char *prog)
{
	fprintf(stderr, "usage\n");
	exit(1);
}

static void
parse_cmdline(int argc, char **argv)
{
	int index, c;

	opterr = 0;

	for (;;) {
		c = getopt_long(argc, argv, OPTSTR, options, &index);
		if (c == -1)
			break;

		switch (c) {
		case '2':
			opt.dual = true;
			break;
		case 'b':
			opt.nonblock = false;
			break;
		case 'e':
			opt.end_summary = true;
			break;
		case 'f':
			opt.rw_api = RW_FIXED;
			break;
		case 'o':
			opt.transport = TRANSPORT_IOU;
			break;
		case 'm':
			opt.rw_api = RW_MSG;
			break;
		case 'p':
			opt.poll = true;
			break;
		case 'P':
			opt.port = atoi(optarg);
			break;
		case 't':
			opt.transport = TRANSPORT_TCP;
			break;
		case 'u':
			opt.transport = TRANSPORT_UDP;
			break;
		case 'x':
			opt.transport = TRANSPORT_XDP;
			break;
		default:
			usage(basename(argv[0]));
		}
	}
}

static void
handle_options(void)
{

	opt.ifindex = if_nametoindex(opt.iface);
	if (!opt.ifindex)
		errx(1, "Interface '%s' does not exist", opt.iface);

	switch (opt.transport) {
	case TRANSPORT_TCP:
		run.socktype = SOCK_STREAM;
		break;
	case TRANSPORT_UDP:
		run.socktype = SOCK_DGRAM;
		break;
	case TRANSPORT_XDP:
		run.socktype = SOCK_DGRAM;
		break;
	case TRANSPORT_IOU:
		run.socktype = SOCK_STREAM;
		break;
	}

	if (opt.use_wakeup)
		opt.bind_flags = XDP_USE_NEED_WAKEUP;
}

typedef void bench_fcn(void);

static bench_fcn *server_fn[] = {
	[TRANSPORT_TCP] = tcp_server,
	[TRANSPORT_UDP] = udp_server,
	[TRANSPORT_XDP] = xdp_server,
	[TRANSPORT_IOU] = iou_server,
};

static bench_fcn *client_fn[] = {
	[TRANSPORT_TCP] = tcp_client,
	[TRANSPORT_UDP] = udp_client,
	[TRANSPORT_XDP] = xdp_client,
	[TRANSPORT_IOU] = iou_client,
};

struct ether_addr cli_mac = { 0x24, 0x8a, 0x07, 0x8b, 0x00, 0x28 };
struct ether_addr srv_mac = { 0x24, 0x8a, 0x07, 0x8b, 0x00, 0xce };

static void
client_init(char *peername)
{
	init(peername);

#if 0
	memcpy(&peer->mac_addr, &srv_mac, sizeof(srv_mac));
	memcpy(&self->mac_addr, &cli_mac, sizeof(cli_mac)));
#endif
}

static void
server_init(void)
{
	init(NULL);

#if 0
	memcpy(&self->mac_addr, &srv_mac, sizeof(srv_mac));
	memcpy(&peer->mac_addr, &cli_mac, sizeof(cli_mac)));
#endif
}

int
main(int argc, char **argv)
{

	initialize();
	parse_cmdline(argc, argv);
	handle_options();

	printf("%s transport,%s%s%s%s%s\n",
	    transport_name[opt.transport],
	    optind == argc ? "server" : argv[optind],
	    opt.nonblock ? ",nonblocking" : ",blocking",
	    opt.poll ? ",poll" : "",
	    opt.rw_api == RW_BASIC ? "" :
	        opt.rw_api == RW_MSG ? ",*msg" : ",fixed",
	    opt.dual ? ",dual" : "");

	if (optind == argc) {
		server_init();
		server_fn[opt.transport]();
	} else {
		client_init(argv[optind]);
		client_fn[opt.transport]();
		statistics();
	}

	return 0;
}
