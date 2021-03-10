/*
 * Copyright © 2017-2020 Michael Forney
 * Copyright © 2021 Duncan Overbruck <mail@duncano.de>
 * 
 * Permission to use, copy, modify, and/or distribute this software for any purpose
 * with or without fee is hereby granted, provided that the above copyright notice
 * and this permission notice appear in all copies.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS
 * OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
 * TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF
 * THIS SOFTWARE.
*/
#define _GNU_SOURCE
#include <sys/stat.h>
#include <sys/wait.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <spawn.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <unistd.h>
#include "uthash.h"

#ifdef __GLIBC__
size_t strlcpy(char *dst, const char *src, size_t dsize);
#endif

struct pkgname {
	char *name;
	size_t nuse;
	struct srcpkg **use;
	struct srcpkg *srcpkg;
	time_t mtime;
	bool dirty;
	UT_hash_handle hh;
};

struct srcpkg {
	struct pkgname *pkgname;
	char *version;
	char *revision;

	size_t nhostdeps;
	struct pkgname **hostdeps;
	size_t ntargetdeps;
	struct pkgname **targetdeps;
	size_t nsubpkgs;
	struct pkgname **subpkgs;

	time_t depmtime;
	time_t deperrmtime;
	time_t logmtime;
	time_t logerrmtime;

	size_t nblock;

	enum {
		FLAG_WORK  = 1 << 0,
		FLAG_CYCLE = 1 << 1,
		FLAG_DEPS  = 1 << 2,
		FLAG_DIRTY = 1 << 3,
		FLAG_SKIP  = 1 << 4,
	} flags;

	struct srcpkg *allnext;
	struct srcpkg *worknext;
};

enum {
	MTIME_UNKNOWN = -1,
	MTIME_MISSING = -2,
};

struct pool {
	size_t maxjobs;
	size_t numjobs;
	struct srcpkg *work;
};

static const char *distdir = "/home/duncan/void-packages";
static char *xbps_src = "/home/duncan/void-packages/xbps-src";

static struct pkgname *pkgnames;
static struct srcpkg *srcpkgs;

static size_t numtotal;
static bool explain;

static void *
xzmalloc(size_t sz)
{
	void *p = calloc(1, sz);
	if (!p) {
		perror("xzmalloc");
		exit(1);
	}
	return p;
}

static char *
xstrdup(const char *s)
{
	char *p = strdup(s);
	if (!p) {
		perror("xstrdup");
		exit(1);
	}
	return p;
}

static void
xsnprintf(char *buf, size_t buflen, const char *fmt, ...)
{
	va_list ap;
	int l;

	va_start(ap, fmt);
	l = vsnprintf(buf, buflen, fmt, ap);
	va_end(ap);

	if (l < 0 || (size_t)l >= buflen) {
		fprintf(stderr, "snprintf: %s: buffer too small\n", fmt);
		exit(1);
	}
}

static struct pkgname *
mkpkgname(const char *name)
{
	struct pkgname *n;
	HASH_FIND_STR(pkgnames, name, n);
	if (!n) {
		n = xzmalloc(sizeof *n);
		n->name = xstrdup(name);
		n->mtime = MTIME_UNKNOWN;
		n->dirty = false;
		HASH_ADD_STR(pkgnames, name, n);
	}
	return n;
}

static struct srcpkg *
mksrcpkg(struct pkgname *pkgname)
{
	struct srcpkg *srcpkg;
	srcpkg = xzmalloc(sizeof *srcpkg);
	srcpkg->pkgname = pkgname;
	srcpkg->allnext = srcpkgs;
	srcpkg->depmtime = MTIME_UNKNOWN;
	srcpkg->deperrmtime = MTIME_UNKNOWN;
	srcpkg->logmtime = MTIME_UNKNOWN;
	srcpkg->logerrmtime = MTIME_UNKNOWN;
	srcpkgs = srcpkg;
	return srcpkg;
}

static void
pkgnamestat(struct pkgname *pkgname)
{
	char buf[PATH_MAX];
	struct stat st;

	pkgname->mtime = MTIME_MISSING;
	xsnprintf(buf, sizeof buf, "%s/srcpkgs/%s", distdir, pkgname->name);
	if (lstat(buf, &st) == -1) {
		if (errno == ENOENT) {
			const char *p;
			if ((p = strrchr(pkgname->name, '-'))) {
				/* XXX: -32bit should be handled differently */
				if (strcmp(p, "-dbg") == 0 || strcmp(p, "-32bit") == 0) {
					strlcpy(buf, pkgname->name, p-pkgname->name+1);
					struct pkgname *srcpkgname = mkpkgname(buf);
					if (!srcpkgname->srcpkg) {
						srcpkgname->srcpkg = mksrcpkg(srcpkgname);
					}
					pkgname->srcpkg = srcpkgname->srcpkg;
				}
			}
		}
		fprintf(stderr, "lstat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}
	if (st.st_mode & S_IFLNK) {
		/* if this is a subpackage, use the symlinks mtime */
		pkgname->mtime = st.st_mtime;
		return;
	}
	if (st.st_mode & S_IFDIR) {
		/* for source packages, use the templates mtime */
		xsnprintf(buf, sizeof buf, "%s/srcpkgs/%s/template", distdir, pkgname->name);
		if (lstat(buf, &st) == -1) {
			fprintf(stderr, "stat: %s: %s\n", buf, strerror(errno));
			exit(1);
		}
		pkgname->mtime = st.st_mtime;
	}
}

static void
depstat(struct srcpkg *srcpkg)
{
	char buf[PATH_MAX];
	struct stat st;

	srcpkg->depmtime = MTIME_MISSING;
	srcpkg->deperrmtime = MTIME_MISSING;

	xsnprintf(buf, sizeof buf, "deps/%s.dep", srcpkg->pkgname->name);
	if (stat(buf, &st) == -1) {
		if (errno != ENOENT) {
			perror("stat");
			exit(1);
		}
	} else {
		srcpkg->depmtime = st.st_mtime;
	}
	xsnprintf(buf, sizeof buf, "deps/%s.err", srcpkg->pkgname->name);
	if (stat(buf, &st) == -1) {
		if (errno != ENOENT) {
			perror("stat");
			exit(1);
		}
	} else {
		srcpkg->deperrmtime = st.st_mtime;
	}
}

static void
logstat(struct srcpkg *srcpkg)
{
	char buf[PATH_MAX];
	struct stat st;

	srcpkg->logmtime = MTIME_MISSING;
	srcpkg->logerrmtime = MTIME_MISSING;

	if (!srcpkg->version || !srcpkg->revision)
		return;

	xsnprintf(buf, sizeof buf, "logs/%s-%s_%s.log", srcpkg->pkgname->name, srcpkg->version, srcpkg->revision);
	if (stat(buf, &st) == 0) {
		srcpkg->logmtime = st.st_mtime;
	} else if (errno != ENOENT) {
		fprintf(stderr, "stat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}

	xsnprintf(buf, sizeof buf, "logs/%s-%s_%s.err", srcpkg->pkgname->name, srcpkg->version, srcpkg->revision);
	if (stat(buf, &st) == 0) {
		srcpkg->logerrmtime = st.st_mtime;
	} else if (errno != ENOENT) {
		fprintf(stderr, "stat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}
}

static struct pkgname *
addpkg(const char *name)
{
	char buf[PATH_MAX];
	struct pkgname *pkgname;

	pkgname = mkpkgname(name);
	if (pkgname->srcpkg)
		return pkgname;

	xsnprintf(buf, sizeof buf, "%s/srcpkgs/%s", distdir, name);

	struct stat st;
	if (lstat(buf, &st) == -1) {
		if (errno == ENOENT) {
			const char *p;
			if ((p = strrchr(name, '-'))) {
				if (strcmp(p, "-dbg") == 0 || strcmp(p, "-32bit") == 0) {
					strlcpy(buf, name, p-name+1);
					struct pkgname *srcpkgname = mkpkgname(buf);
					if (!srcpkgname->srcpkg) {
						srcpkgname->srcpkg = mksrcpkg(srcpkgname);
					}
					pkgname->srcpkg = srcpkgname->srcpkg;
					return pkgname;
				}
			}
		}
		fprintf(stderr, "lstat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}
	if (st.st_mode & S_IFDIR) {
		xsnprintf(buf, sizeof buf, "%s/srcpkgs/%s/template", distdir, name);
		if (stat(buf, &st) == -1) {
			fprintf(stderr, "perror: %s: %s\n", buf, strerror(errno));
			exit(1);
		}
		pkgname->mtime = st.st_mtime;
		pkgname->srcpkg = mksrcpkg(pkgname);
		return pkgname;
	}
	if (st.st_mode & S_IFLNK) {
		pkgname->mtime = st.st_mtime;
		ssize_t len;
		if ((len = readlink(buf, buf, sizeof buf)) == -1) {
			perror("readlink");
			exit(1);
		}

		if ((size_t)len >= sizeof buf) {
			errno = ENOBUFS;
			perror("readlink");
			exit(1);
		}
		buf[len] = '\0';

		if (len > 0 && buf[len-1] == '/') {
			fprintf(stderr, "warn: symlink `%s/srcpkgs/%s` contains trailing slash.\n", distdir, name);
			buf[len-1] = '\0';
		}
		struct pkgname *srcpkgname = mkpkgname(buf);
		if (!srcpkgname->srcpkg) {
			srcpkgname->srcpkg = mksrcpkg(srcpkgname);
		}
		pkgname->srcpkg = srcpkgname->srcpkg;
	} else {
		fprintf(stderr, "unexpected file type: %s\n", buf);
		exit(1);
	}

	return pkgname;
}

static void
pkgnameuse(struct pkgname *pkgname, struct srcpkg *srcpkg)
{
	pkgname->use = reallocarray(pkgname->use, pkgname->nuse+1, sizeof *pkgname->use);
	if (!pkgname->use) {
		perror("reallocarray");
		exit(1);
	}
	pkgname->use[pkgname->nuse++] = srcpkg;
}

static struct srcpkg *work;

static void
addhostdep(struct srcpkg *srcpkg, const char *name)
{
	struct pkgname *dep = addpkg(name);
	srcpkg->hostdeps = reallocarray(srcpkg->hostdeps, srcpkg->nhostdeps+1, sizeof *srcpkg->hostdeps);
	if (!srcpkg->hostdeps) {
		perror("reallocarray");
		exit(1);
	}
	srcpkg->hostdeps[srcpkg->nhostdeps++] = dep;
	pkgnameuse(dep, srcpkg);
}

static void
addtargetdep(struct srcpkg *srcpkg, const char *name)
{
	struct pkgname *dep = addpkg(name);
	srcpkg->targetdeps = reallocarray(srcpkg->targetdeps, srcpkg->ntargetdeps+1, sizeof *srcpkg->targetdeps);
	if (!srcpkg->targetdeps) {
		perror("reallocarray");
		exit(1);
	}
	srcpkg->targetdeps[srcpkg->ntargetdeps++] = dep;
	pkgnameuse(dep, srcpkg);
}

static int
readdeps(struct srcpkg *srcpkg, FILE *fp)
{
	const char *d;
	char *line = NULL;
	size_t linelen = 0;
	ssize_t rd;
	enum {
		Sdefault = 0x00,
		Sarray   = 0x01,
		Shostdep = 0x20,
		Smakedep = 0x40,
		Stargdep = 0x60,
		Ssubpkgs = 0xC0,
	} state = Sdefault;

	while ((rd = getdelim(&line, &linelen, '\n', fp)) != -1) {
		if (line[rd-1] == '\n')
			line[rd-1] = '\0';
		if (state & Sarray) {
			if (*line == ' ') {
				switch (state & ~Sarray) {
				case Shostdep:
					addhostdep(srcpkg, line+1);
					break;
				case Smakedep:
					/* fallthrough */
				case Stargdep:
					addtargetdep(srcpkg, line+1);
				case Ssubpkgs:
					continue;
				default:
					continue;
				}
				continue;
			}
			state = Sdefault;
		}
		if ((d = strchr(line, ':'))) {
			if (d[1] == '\0') {
				state = Sarray;
				if (strncmp("hostmakedepends", line, d-line) == 0) {
					state |= Shostdep;
				} else if (strncmp("makedepends", line, d-line) == 0) {
					state |= Smakedep;
				} else if (strncmp("depends", line, d-line) == 0) {
					state |= Stargdep;
				} else if (strncmp("subpackages", line, d-line) == 0) {
					state |= Ssubpkgs;
				}
				continue;
			}
		} else {
			free(line);
			return -1;
		}
		if (strncmp("pkgname", line, d-line) == 0) {
			/* XXX: check if pkgname matches? */
		} else if (strncmp("version", line, d-line) == 0) {
			free(srcpkg->version);
			srcpkg->version = xstrdup(d+2);
		} else if (strncmp("revision", line, d-line) == 0) {
			free(srcpkg->revision);
			srcpkg->revision = xstrdup(d+2);
		} else {
			/* fprintf(stderr, "key: %.*s value: %s\n", d-line, line, d+2); */
		}
	}
	free(line);
}

static void
queue(struct srcpkg *srcpkg)
{
	struct srcpkg **front = &work;
	srcpkg->worknext = *front;
	*front = srcpkg;
}

static void
loaddeps(struct srcpkg *srcpkg)
{
	char path[PATH_MAX];
	struct stat st;

	if (srcpkg->flags & FLAG_DEPS)
		return;

	xsnprintf(path, sizeof path, "deps/%s.dep", srcpkg->pkgname->name);
	FILE *fp = fopen(path, "r");
	if (fp == NULL) {
		fprintf(stderr, "fopen: %s: %s", path, strerror(errno));
		exit(1);
	}
	if (readdeps(srcpkg, fp) == -1) {
		perror("readdeps");
		exit(1);
	}
	fclose(fp);

	srcpkg->flags |= FLAG_DEPS;
}

static void
pkgnamedone(struct pkgname *pkgname, bool prune)
{
	for (size_t i = 0; i < pkgname->nuse; ++i) {
		struct srcpkg *srcpkg = pkgname->use[i];
		/* skip edges not used in this build */
		if (!(srcpkg->flags & FLAG_WORK))
			continue;
		if (--srcpkg->nblock == 0)
			queue(srcpkg);
	}
}

static size_t maxjobs = 1;

static size_t maxfail = -1;
static size_t numfail = 0;
static size_t numfinished = 0;

static bool dryrun = false;

struct job {
	size_t next;
	int status;
	struct srcpkg *srcpkg;
	pid_t pid;
	bool failed;
};

static void buildadd(struct pkgname *pkgname);

static void
gendepdone(struct job *j)
{
	char path1[PATH_MAX], path2[PATH_MAX];
	const char *name = j->srcpkg->pkgname->name;

	if (WIFEXITED(j->status) && WEXITSTATUS(j->status) != 0) {
		fprintf(stderr, "job failed: %s\n", name);
		j->failed = true;
	}

	if (j->failed) {
		xsnprintf(path1, sizeof path1, "deps/%s.dep.tmp", name);
		if (unlink(path1) == -1) {
			if (errno != ENOENT) {
				fprintf(stderr, "unlink: %s: %s\n", path1, strerror(errno));
				exit(1);
			}
		}
		xsnprintf(path1, sizeof path1, "deps/%s.err.tmp", name);
		xsnprintf(path2, sizeof path2, "deps/%s.err", name);
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}
	} else {
		xsnprintf(path1, sizeof path1, "deps/%s.err.tmp", name);
		if (unlink(path1) == -1) {
			if (errno != ENOENT) {
				fprintf(stderr, "unlink: %s: %s\n", path1, strerror(errno));
				exit(1);
			}
		}

		xsnprintf(path1, sizeof path1, "deps/%s.dep.tmp", name);
		xsnprintf(path2, sizeof path2, "deps/%s.dep", name);
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}

		j->srcpkg->flags &= ~FLAG_WORK;
		depstat(j->srcpkg);
		buildadd(j->srcpkg->pkgname);
	}
}

static int
gendepstart(struct job *j, struct srcpkg *srcpkg)
{
	extern char **environ;
	char path[PATH_MAX];
	posix_spawn_file_actions_t actions;
	char *const argv[] = {xbps_src, "dbulk-dump", srcpkg->pkgname->name, NULL};
	int stdoutfd, stderrfd;

	j->failed = false;
	j->srcpkg = srcpkg;
	j->status = 0;

	xsnprintf(path, sizeof path, "deps/%s.dep.tmp", srcpkg->pkgname->name);
	stdoutfd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (stdoutfd == -1) {
		fprintf(stderr, "open: %s: %s\n", path, strerror(errno));
		exit(1);
	}
	xsnprintf(path, sizeof path, "deps/%s.err.tmp", srcpkg->pkgname->name);
	stderrfd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (stderrfd == -1) {
		fprintf(stderr, "open: %s: %s\n", path, strerror(errno));
		exit(1);
	}

	if ((errno = posix_spawn_file_actions_init(&actions))) {
		perror("posix_spawn_file_actions_init");
		goto err1;
	}
	if ((errno = posix_spawn_file_actions_addopen(&actions, 0, "/dev/null", O_RDONLY, 0))) {
		perror("posix_spawn_file_actions_addopen");
		goto err2;
	}
	if ((errno = posix_spawn_file_actions_adddup2(&actions, stdoutfd, 1))) {
		perror("posix_spawn_file_actions_adddup2");
		goto err2;
	}
	if ((errno = posix_spawn_file_actions_adddup2(&actions, stderrfd, 2))) {
		perror("posix_spawn_file_actions_adddup2");
		goto err2;
	}
	if ((errno = posix_spawn(&j->pid, argv[0], &actions, NULL, argv, environ))) {
		fprintf(stderr, "posix_spawn: %s: %s\n", srcpkg->pkgname->name, strerror(errno));
		goto err2;
	}
	posix_spawn_file_actions_destroy(&actions);
	close(stdoutfd);
	close(stderrfd);

	return 0;

err2:
	posix_spawn_file_actions_destroy(&actions);
err1:
	close(stdoutfd);
	close(stderrfd);
err0:
	return -1;
}

static void
srcpkgdone(struct srcpkg *srcpkg)
{
	pkgnamedone(srcpkg->pkgname, false);
	for (size_t i = 0; i < srcpkg->nsubpkgs; ++i) {
		pkgnamedone(srcpkg->subpkgs[i], false);
	}
}

static void
builddone(struct job *j)
{
	char path1[PATH_MAX], path2[PATH_MAX];
	const char *name = j->srcpkg->pkgname->name;
	const char *version = j->srcpkg->version;
	const char *revision = j->srcpkg->revision;

	if (WIFEXITED(j->status) && WEXITSTATUS(j->status) != 0) {
		fprintf(stderr, "job failed: %s\n", j->srcpkg->pkgname->name);
		j->failed = true;
	}

	if (j->failed) {
		xsnprintf(path1, sizeof path1, "logs/%s-%s_%s.tmp", name, version, revision);
		xsnprintf(path2, sizeof path2, "logs/%s-%s_%s.err", name, version, revision);
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}
	} else {
		xsnprintf(path1, sizeof path1, "logs/%s-%s_%s.tmp", name, version, revision);
		xsnprintf(path2, sizeof path2, "logs/%s-%s_%s.log", name, version, revision);
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}

		srcpkgdone(j->srcpkg);
	}
}

static int
buildstart(struct job *j, struct srcpkg *srcpkg)
{
	extern char **environ;
	char path[PATH_MAX];
	posix_spawn_file_actions_t actions;
	char *const argv[] = {xbps_src, "pkg", "-1Et", "-j", "4", srcpkg->pkgname->name, NULL};
	int fd;

	j->failed = false;
	j->srcpkg = srcpkg;
	j->status = 0;

	xsnprintf(path, sizeof path, "logs/%s-%s_%s.tmp", srcpkg->pkgname->name, srcpkg->version, srcpkg->revision);
	fd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (fd == -1) {
		perror("open");
		exit(1);
	}

	if ((errno = posix_spawn_file_actions_init(&actions))) {
		perror("posix_spawn_file_actions_init");
		goto err1;
	}
	if ((errno = posix_spawn_file_actions_addopen(&actions, 0, "/dev/null", O_RDONLY, 0))) {
		perror("posix_spawn_file_actions_addopen");
		goto err2;
	}
	if ((errno = posix_spawn_file_actions_adddup2(&actions, fd, 1))) {
		perror("posix_spawn_file_actions_adddup2");
		goto err2;
	}
	if ((errno = posix_spawn_file_actions_adddup2(&actions, fd, 2))) {
		perror("posix_spawn_file_actions_adddup2");
		goto err2;
	}
	if ((errno = posix_spawn(&j->pid, argv[0], &actions, NULL, argv, environ))) {
		fprintf(stderr, "posix_spawn: %s: %s\n", srcpkg->pkgname->name, strerror(errno));
		goto err2;
	}
	posix_spawn_file_actions_destroy(&actions);
	close(fd);

	return 0;

err2:
	posix_spawn_file_actions_destroy(&actions);
err1:
	close(fd);
err0:
	return -1;
}

static int
jobstart(struct job *j, struct srcpkg *srcpkg)
{
	if (srcpkg->flags & FLAG_DEPS) {
		return buildstart(j, srcpkg);
	} else {
		return gendepstart(j, srcpkg);
	}
}

static void
jobdone(struct job *j)
{
	numfinished++;
	if (WIFEXITED(j->status)) {
		; /* exit status is handled by builddone and gendepdone */
	} else if (WIFSIGNALED(j->status)) {
		fprintf(stderr, "job terminated due to signal %d: %s\n", WTERMSIG(j->status), j->srcpkg->pkgname->name);
		j->failed = true;
	} else {
		/* cannot happen according to POSIX */
		fprintf(stderr, "job status unknown: %s\n", j->srcpkg->pkgname->name);
		j->failed = true;
	}
	if (j->srcpkg->flags & FLAG_DEPS) {
		builddone(j);
	} else {
		gendepdone(j);
	}
}

static void
build(void)
{
	struct job *jobs;
	size_t numfail = 0;
	size_t next = 0, numjobs = 0;

	jobs = calloc(maxjobs, sizeof *jobs);
	if (!jobs) {
		perror("calloc");
		exit(1);
	}
	for (size_t i = 0; i < maxjobs; ++i) {
		jobs[i].next = i + 1;
	}

	for (;;) {
again:
		while (work && numjobs < maxjobs) {
			struct srcpkg *srcpkg = work;
			work = work->worknext;
			if (dryrun) {
				pkgnamedone(srcpkg->pkgname, false);
				for (size_t i = 0; i < srcpkg->nsubpkgs; i++) {
					pkgnamedone(srcpkg->subpkgs[i], false);
				}
				continue;
			}

			if (jobstart(&jobs[next], srcpkg) == -1) {
				fprintf(stderr, "job failed to start: %s\n", srcpkg->pkgname->name);
				numfail++;
				continue;
			}
			next = jobs[next].next;
			numjobs++;
		}

		if (numjobs == 0)
			break;

		int status;
		pid_t pid = waitpid(-1, &status, 0);
		if (pid == -1) {
			perror("waitpid");
			exit(1);
		}

		for (size_t i = 0; i < maxjobs; i++) {
			if (jobs[i].pid != pid)
				continue;
			const char *action = jobs[i].srcpkg->flags & FLAG_DEPS ? "build package" : "generated dependencies for";
			jobs[i].status = status;
			jobdone(&jobs[i]);
			numjobs--;
			jobs[i].next = next;
			jobs[i].pid = -1;
			next = i;
			if (jobs[i].failed)
				numfail++;
			fprintf(stderr, "[%zu/%zu] %s %s\n", numfinished, numtotal, action, jobs[i].srcpkg->pkgname->name);
			goto again;
		}
	}
}

static void
scan(void)
{
	char buf[PATH_MAX];
	DIR *dp;
	struct dirent *ent;
	int dirfd;

	xsnprintf(buf, sizeof buf, "%s/srcpkgs", distdir);

	if ((dirfd = open(buf, O_DIRECTORY)) == -1) {
		fprintf(stderr, "open: %s: %s", buf, strerror(errno));
		exit(1);
	}

	dp = fdopendir(dirfd);
	if (!dp) {
		fprintf(stderr, "fdopendir: %s: %s", buf, strerror(errno));
		exit(1);
	}

	while ((ent = readdir(dp))) {
		struct stat st;
		if (*ent->d_name == '.')
			continue;
		if (fstatat(dirfd, ent->d_name, &st, AT_SYMLINK_NOFOLLOW) == -1) {
			perror("fstat");
			exit(1);
		}

		struct pkgname *pkgname = mkpkgname(ent->d_name);
		pkgname->mtime = st.st_mtime;
		struct srcpkg *srcpkg = pkgname->srcpkg;

		if (st.st_mode & S_IFDIR) {
			/* setup_pkg_target(n); */
		} else if (st.st_mode & S_IFLNK) {
			ssize_t len;
			if ((len = readlinkat(dirfd, ent->d_name, buf, sizeof buf)) == -1) {
				perror("readlink");
				exit(1);
			}
			if ((size_t)len >= sizeof buf) {
				errno = ENOBUFS;
				perror("readlink");
				exit(1);
			}
			buf[len] = '\0';

			if (len > 0 && buf[len-1] == '/') {
				fprintf(stderr, "warn: symlink `%s/srcpkgs/%s` contains trailing slash.\n", distdir, ent->d_name);
				buf[len-1] = '\0';
			}
			struct pkgname *srcpkgname = mkpkgname(buf);
			if (!srcpkgname->srcpkg) {
				srcpkgname->srcpkg = mksrcpkg(srcpkgname);
			}
		}
	}
	closedir(dp);
	close(dirfd);
}

static int
_buildadd(struct pkgname *pkgname)
{
	struct srcpkg *srcpkg = pkgname->srcpkg;
	int rv = 0;

	if (!srcpkg) {
		srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
		if (explain)
			fprintf(stderr, "explain: %s: skipping, no template to build package\n", pkgname->name);
		rv = ENOENT;
		goto out;
	}
	if (srcpkg->flags & FLAG_CYCLE) {
		srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
		if (explain)
			fprintf(stderr, "explain: %s: skipping, dependency cycle involving: %s", pkgname->name, pkgname->name);
		rv = ELOOP;
		goto out;
	}
	if (srcpkg->flags & FLAG_WORK)
		return 0;

	srcpkg->flags |= FLAG_CYCLE | FLAG_WORK;

	if (srcpkg->pkgname->mtime == MTIME_UNKNOWN)
		pkgnamestat(srcpkg->pkgname);
	for (size_t i = 0; i < srcpkg->nsubpkgs; i++) {
		struct pkgname *n1 = srcpkg->subpkgs[i];
		if (n1->mtime == MTIME_UNKNOWN)
			pkgnamestat(n1);
	}

	if (srcpkg->depmtime == MTIME_UNKNOWN)
		depstat(srcpkg);

	/* dep file missing or outdated */
	if (srcpkg->depmtime < srcpkg->pkgname->mtime) {
		/* depfile error missing or older than template, regenerate it */
		if (srcpkg->deperrmtime < srcpkg->pkgname->mtime) {
			/* XXX: order is irrelevant, but would ordering still make sense
			 * to prioritize building packages over generating deps in
			 * case we have an old dep file? */
			if (explain)
				fprintf(stderr, "explain %s: dependency file %s\n", srcpkg->pkgname->name,
				    srcpkg->depmtime == MTIME_MISSING ? "missing" : "older than template");
			srcpkg->flags |= FLAG_DIRTY;
			srcpkg->nblock = 0;
			goto out;
		} else {
			srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
			if (explain)
				fprintf(stderr, "explain %s: skipping, template unchanged since previous error\n", srcpkg->pkgname->name);
			goto out;
		}
	}

	if (srcpkg->depmtime > MTIME_MISSING)
		loaddeps(srcpkg);

	if ((srcpkg->flags & FLAG_DEPS)) {

		logstat(srcpkg);
		if (srcpkg->logmtime == MTIME_MISSING) {
			if (srcpkg->logerrmtime == MTIME_MISSING) {
				/* Build the package if log and error mtime are missing */
				if (explain)
					fprintf(stderr, "explain %s: missing\n", srcpkg->pkgname->name);
				srcpkg->flags |= FLAG_DIRTY;
			} else if (srcpkg->logerrmtime < srcpkg->pkgname->mtime) {
				/* Build the package if log mtime is missing and error mtime is older than the template */
				if (explain)
					fprintf(stderr, "explain %s: reattempt, template changed since previous error\n", srcpkg->pkgname->name);
				srcpkg->flags |= FLAG_DIRTY;
			} else {
				srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
				if (explain)
					fprintf(stderr, "explain %s: skipping, template unchanged since previous error\n", srcpkg->pkgname->name);
				goto out;
			}
		}

		for (size_t i = 0; i < srcpkg->nhostdeps; i++) {
			struct pkgname *n1 = srcpkg->hostdeps[i];
			if ((rv = _buildadd(n1)) != 0) {
				if (rv == ELOOP) {
					srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
					fprintf(stderr, " <- %s", pkgname->name);
				}
				goto out;
			}
			if (n1->dirty)
				srcpkg->nblock++;
		}

		for (size_t i = 0; i < srcpkg->ntargetdeps; i++) {
			struct pkgname *n1 = srcpkg->targetdeps[i];
			if ((rv = _buildadd(n1)) != 0) {
				if (rv == ELOOP) {
					srcpkg->flags |= FLAG_SKIP|FLAG_DIRTY;
					fprintf(stderr, " <- %s", pkgname->name);
				}
				goto out;
			}
			if (n1->dirty)
				srcpkg->nblock++;
		}
	}

out:
	if (srcpkg->flags & FLAG_DIRTY) {
		/* Missing deps or missing package, mark all packages as dirty */
		srcpkg->pkgname->dirty = true;
		for (size_t i = 0; i < srcpkg->nsubpkgs; i++) {
			struct pkgname *n1 = srcpkg->subpkgs[i];
			n1->dirty = true;
		}

		if (!(srcpkg->flags & FLAG_SKIP)) {
			if (srcpkg->nblock == 0)
				queue(srcpkg);
			numtotal++;
		}
	}
	srcpkg->flags &= ~FLAG_CYCLE;
	return rv;
}

static void
buildadd(struct pkgname *pkgname)
{
	int rv;
	if ((rv = _buildadd(pkgname)) != 0) {
		if (rv == ELOOP) {
			fprintf(stderr, "\n");
			return;
		}
	}
}
int
main(int argc, char *argv[])
{
	int c;
	unsigned long ul;

	while ((c = getopt(argc, argv, "dj:n")) != -1)
		switch (c) {
		case 'd':
			explain = true;
			break;
		case 'j':
			errno = 0;
			ul = strtoul(optarg, NULL, 10);
			if (errno != 0) {
				fprintf(stderr, "strtoul: %s: %s\n", optarg, strerror(errno));
				exit(1);
			}
			maxjobs = ul;
			break;
		case 'n':
			dryrun = true;
			break;
		default:
			fprintf(stderr, "usage: %s [-den] [-j jobs] [target...]\n", *argv);
		}

	argc -= optind;
	argv += optind;

	if (mkdir("logs", 0755) == -1 && errno != EEXIST) {
		fprintf(stderr, "mkdir: %s: %s\n", "logs", strerror(errno));
		exit(1);
	}
	if (mkdir("deps", 0755) == -1 && errno != EEXIST) {
		fprintf(stderr, "mkdir: %s: %s\n", "deps", strerror(errno));
		exit(1);
	}

	if (argc > 0) {
		for (int i = 0; i < argc; i++) {
			buildadd(addpkg(argv[i]));
		}
	} else {
		scan();
		/* build all packages */
		for (struct srcpkg *srcpkg = srcpkgs; srcpkg; srcpkg = srcpkg->allnext) {
			buildadd(srcpkg->pkgname);
		}
	}

	build();
	return 0;
}
