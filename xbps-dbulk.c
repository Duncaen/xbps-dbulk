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

struct builder {
	char *arch;
	struct builder *host;
	char *masterdir;
	UT_hash_handle hh;
};

struct pkgname {
	char *name;
	struct pkgname *srcpkg;
	size_t nuse;
	struct build **use;
	size_t nbuilds;
	struct build **builds;
	time_t mtime;
	bool dirty;
	UT_hash_handle hh;
};

struct build {
	struct pkgname *pkgname;
	char *version;
	char *revision;
	struct builder *builder;

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

	struct build *allnext;
	struct build *worknext;
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

static const char *distdir;

static struct pkgname *pkgnames;
static struct builder *builders;
static struct build *builds;
static struct build *work;

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

static struct builder *
mkbuilder(const char *arch)
{
	struct builder *b;
	HASH_FIND_STR(builders, arch, b);
	if (!b) {
		b = xzmalloc(sizeof *b);
		b->arch = xstrdup(arch);
		HASH_ADD_STR(builders, arch, b);
	}
	return b;
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
					pkgname->srcpkg = mkpkgname(buf);
					if (pkgname->srcpkg->mtime == MTIME_UNKNOWN)
						pkgnamestat(pkgname->srcpkg);
					/* use the source packages mtime */
					pkgname->mtime = pkgname->srcpkg->mtime;
					return;
				}
			}
		}
		fprintf(stderr, "lstat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}
	if (st.st_mode & S_IFLNK) {
		/* if this is a subpackage, use the symlinks mtime */
		pkgname->mtime = st.st_mtime;
		if (!pkgname->srcpkg) {
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
				fprintf(stderr, "warn: symlink `%s/srcpkgs/%s` contains trailing slash.\n", distdir, pkgname->name);
				buf[len-1] = '\0';
			}
			pkgname->srcpkg = mkpkgname(buf);
			if (pkgname->srcpkg->mtime == MTIME_UNKNOWN)
				pkgnamestat(pkgname->srcpkg);
		}
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
depstat(struct build *build)
{
	char buf[PATH_MAX];
	struct stat st;

	build->depmtime = MTIME_MISSING;
	build->deperrmtime = MTIME_MISSING;

	if (build->builder->host)
		xsnprintf(buf, sizeof buf, "deps/%s@%s/%s.dep", build->builder->arch, build->builder->host->arch, build->pkgname->name);
	else
		xsnprintf(buf, sizeof buf, "deps/%s/%s.dep", build->builder->arch, build->pkgname->name);
	if (stat(buf, &st) == -1) {
		if (errno != ENOENT) {
			perror("stat");
			exit(1);
		}
	} else {
		build->depmtime = st.st_mtime;
	}
	if (build->builder->host)
		xsnprintf(buf, sizeof buf, "deps/%s@%s/%s.err", build->builder->arch, build->builder->host->arch, build->pkgname->name);
	else
		xsnprintf(buf, sizeof buf, "deps/%s/%s.err", build->builder->arch, build->pkgname->name);
	if (stat(buf, &st) == -1) {
		if (errno != ENOENT) {
			perror("stat");
			exit(1);
		}
	} else {
		build->deperrmtime = st.st_mtime;
	}
}

static void
logstat(struct build *build)
{
	char buf[PATH_MAX];
	struct stat st;

	build->logmtime = MTIME_MISSING;
	build->logerrmtime = MTIME_MISSING;

	if (!build->version || !build->revision)
		return;

	if (build->builder->host)
		xsnprintf(buf, sizeof buf, "logs/%s@%s/%s-%s_%s.log", build->builder->arch, build->builder->host->arch, build->pkgname->name, build->version, build->revision);
	else
		xsnprintf(buf, sizeof buf, "logs/%s/%s-%s_%s.log", build->builder->arch, build->pkgname->name, build->version, build->revision);
	if (stat(buf, &st) == 0) {
		build->logmtime = st.st_mtime;
	} else if (errno != ENOENT) {
		fprintf(stderr, "stat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}

	if (build->builder->host)
		xsnprintf(buf, sizeof buf, "logs/%s@%s/%s-%s_%s.err", build->builder->arch, build->builder->host->arch, build->pkgname->name, build->version, build->revision);
	else
		xsnprintf(buf, sizeof buf, "logs/%s/%s-%s_%s.err", build->builder->arch, build->pkgname->name, build->version, build->revision);
	if (stat(buf, &st) == 0) {
		build->logerrmtime = st.st_mtime;
	} else if (errno != ENOENT) {
		fprintf(stderr, "stat: %s: %s\n", buf, strerror(errno));
		exit(1);
	}
}

static void
pkgnamebuild(struct pkgname *pkgname, struct build *build)
{
	pkgname->builds = reallocarray(pkgname->builds, pkgname->nbuilds+1, sizeof *pkgname->builds);
	if (!pkgname->builds) {
		perror("reallocarray");
		exit(1);
	}
	pkgname->builds[pkgname->nbuilds++] = build;
}

static void
pkgnameuse(struct pkgname *pkgname, struct build *build)
{
	pkgname->use = reallocarray(pkgname->use, pkgname->nuse+1, sizeof *pkgname->use);
	if (!pkgname->use) {
		perror("reallocarray");
		exit(1);
	}
	pkgname->use[pkgname->nuse++] = build;
}

static void
addhostdep(struct build *build, const char *name)
{
	struct pkgname *dep = mkpkgname(name);
	build->hostdeps = reallocarray(build->hostdeps, build->nhostdeps+1, sizeof *build->hostdeps);
	if (!build->hostdeps) {
		perror("reallocarray");
		exit(1);
	}
	build->hostdeps[build->nhostdeps++] = dep;
	pkgnameuse(dep, build);
}

static void
addtargetdep(struct build *build, const char *name)
{
	struct pkgname *dep = mkpkgname(name);
	build->targetdeps = reallocarray(build->targetdeps, build->ntargetdeps+1, sizeof *build->targetdeps);
	if (!build->targetdeps) {
		perror("reallocarray");
		exit(1);
	}
	build->targetdeps[build->ntargetdeps++] = dep;
	pkgnameuse(dep, build);
}

static void
addsubpkg(struct build *build, const char *name)
{
	struct pkgname *sub = mkpkgname(name);
	build->subpkgs = reallocarray(build->subpkgs, build->nsubpkgs+1, sizeof *build->subpkgs);
	if (!build->subpkgs) {
		perror("reallocarray");
		exit(1);
	}
	build->subpkgs[build->nsubpkgs++] = sub;
}

static int
readdeps(struct build *build, FILE *fp)
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
					addhostdep(build, line+1);
					break;
				case Smakedep:
					/* fallthrough */
				case Stargdep:
					addtargetdep(build, line+1);
					break;
				case Ssubpkgs:
					addsubpkg(build, line+1);
					break;
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
			free(build->version);
			build->version = xstrdup(d+2);
		} else if (strncmp("revision", line, d-line) == 0) {
			free(build->revision);
			build->revision = xstrdup(d+2);
		} else {
			/* fprintf(stderr, "key: %.*s value: %s\n", d-line, line, d+2); */
		}
	}
	free(line);
}

static void
queue(struct build *build)
{
	struct build **front = &work;
	build->worknext = *front;
	*front = build;
}

static void
loaddeps(struct build *build)
{
	char path[PATH_MAX];
	struct stat st;

	if (build->flags & FLAG_DEPS)
		return;

	if (build->builder->host)
		xsnprintf(path, sizeof path, "deps/%s@%s/%s.dep", build->builder->arch, build->builder->host->arch, build->pkgname->name);
	else
		xsnprintf(path, sizeof path, "deps/%s/%s.dep", build->builder->arch, build->pkgname->name);
	FILE *fp = fopen(path, "r");
	if (fp == NULL) {
		fprintf(stderr, "fopen: %s: %s\n", path, strerror(errno));
		exit(1);
	}
	if (readdeps(build, fp) == -1) {
		perror("readdeps");
		exit(1);
	}
	fclose(fp);

	build->flags |= FLAG_DEPS;
}

static size_t maxjobs = 1;

static size_t maxfail = -1;
static size_t numfail = 0;
static size_t numfinished = 0;

static bool dryrun = false;

struct job {
	size_t next;
	int status;
	struct build *build;
	pid_t pid;
	bool failed;
};

static void buildadd(struct pkgname *pkgname, struct builder *builder);

static void
gendepdone(struct job *j)
{
	char path1[PATH_MAX], path2[PATH_MAX];
	struct build *build = j->build;
	const char *name = build->pkgname->name;

	if (WIFEXITED(j->status) && WEXITSTATUS(j->status) != 0) {
		fprintf(stderr, "job failed: %s\n", name);
		j->failed = true;
	}

	if (j->failed) {
		if (build->builder->host)
			xsnprintf(path1, sizeof path1, "deps/%s@%s/%s.dep.tmp", build->builder->arch, build->builder->host->arch, name);
		else
			xsnprintf(path1, sizeof path1, "deps/%s/%s.dep.tmp", build->builder->arch, name);
		if (unlink(path1) == -1) {
			if (errno != ENOENT) {
				fprintf(stderr, "unlink: %s: %s\n", path1, strerror(errno));
				exit(1);
			}
		}
		if (build->builder->host) {
			xsnprintf(path1, sizeof path1, "deps/%s@%s/%s.err.tmp", build->builder->arch, build->builder->host->arch, name);
			xsnprintf(path2, sizeof path2, "deps/%s@%s/%s.err", build->builder->arch, build->builder->host->arch, name);
		} else {
			xsnprintf(path1, sizeof path1, "deps/%s/%s.err.tmp", build->builder->arch, name);
			xsnprintf(path2, sizeof path2, "deps/%s/%s.err", build->builder->arch, name);
		}
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}
	} else {
		if (build->builder->host)
			xsnprintf(path1, sizeof path1, "deps/%s@%s/%s.err.tmp", build->builder->arch, build->builder->host->arch, name);
		else
			xsnprintf(path1, sizeof path1, "deps/%s/%s.err.tmp", build->builder->arch, name);
		if (unlink(path1) == -1) {
			if (errno != ENOENT) {
				fprintf(stderr, "unlink: %s: %s\n", path1, strerror(errno));
				exit(1);
			}
		}

		if (build->builder->host) {
			xsnprintf(path1, sizeof path1, "deps/%s@%s/%s.dep.tmp", build->builder->arch, build->builder->host->arch, name);
			xsnprintf(path2, sizeof path2, "deps/%s@%s/%s.dep", build->builder->arch, build->builder->host->arch, name);
		} else {
			xsnprintf(path1, sizeof path1, "deps/%s/%s.dep.tmp", build->builder->arch, name);
			xsnprintf(path2, sizeof path2, "deps/%s/%s.dep", build->builder->arch, name);
		}
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}

		build->flags &= ~FLAG_WORK;
		depstat(build);
		buildadd(build->pkgname, build->builder);
	}
}

static int
gendepstart(struct job *j, struct build *build)
{
	extern char **environ;
	char path[PATH_MAX];
	posix_spawn_file_actions_t actions;
	char *Nargv[] = {NULL, "", "dbulk-dump", build->pkgname->name, NULL};
	char *Xargv[] = {NULL, "-a", build->builder->arch, "dbulk-dump", build->pkgname->name, NULL};
	char **argv;
	int stdoutfd, stderrfd;

	j->failed = false;
	j->build = build;
	j->status = 0;

	if (build->builder->host)
		xsnprintf(path, sizeof path, "deps/%s@%s/%s.dep.tmp", build->builder->arch, build->builder->host->arch, build->pkgname->name);
	else
		xsnprintf(path, sizeof path, "deps/%s/%s.dep.tmp", build->builder->arch, build->pkgname->name);
	stdoutfd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (stdoutfd == -1) {
		fprintf(stderr, "open: %s: %s\n", path, strerror(errno));
		exit(1);
	}
	if (build->builder->host)
		xsnprintf(path, sizeof path, "deps/%s@%s/%s.err.tmp", build->builder->arch, build->builder->host->arch, build->pkgname->name);
	else
		xsnprintf(path, sizeof path, "deps/%s/%s.err.tmp", build->builder->arch, build->pkgname->name);
	stderrfd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (stderrfd == -1) {
		fprintf(stderr, "open: %s: %s\n", path, strerror(errno));
		exit(1);
	}

	if (build->builder->host)
		argv = Xargv;
	else
		argv = Nargv;

	xsnprintf(path, sizeof path, "%s/xbps-src", distdir);
	argv[0] = path;

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
		fprintf(stderr, "posix_spawn: %s: %s\n", build->pkgname->name, strerror(errno));
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
pkgnamedone(struct pkgname *pkgname, bool prune)
{
	pkgname->dirty = false;
	for (size_t i = 0; i < pkgname->nuse; i++) {
		struct build *build = pkgname->use[i];
		/* skip edges not used in this build */
		if (!(build->flags & FLAG_WORK))
			continue;
		if (--build->nblock == 0)
			queue(build);
	}
}

static void
builddone(struct job *j)
{
	char path1[PATH_MAX], path2[PATH_MAX];
	struct build *build = j->build;
	const char *name = build->pkgname->name;
	const char *version = build->version;
	const char *revision = build->revision;

	if (WIFEXITED(j->status) && WEXITSTATUS(j->status) != 0) {
		fprintf(stderr, "job failed: %s\n", name);
		j->failed = true;
	}

	if (j->failed) {
		if (build->builder->host) {
			xsnprintf(path1, sizeof path1, "logs/%s@%s/%s-%s_%s.tmp", build->builder->arch, build->builder->host->arch, name, version, revision);
			xsnprintf(path2, sizeof path2, "logs/%s@%s/%s-%s_%s.err", build->builder->arch, build->builder->host->arch, name, version, revision);
		} else {
			xsnprintf(path1, sizeof path1, "logs/%s/%s-%s_%s.tmp", build->builder->arch, name, version, revision);
			xsnprintf(path2, sizeof path2, "logs/%s/%s-%s_%s.err", build->builder->arch, name, version, revision);
		}
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}
	} else {
		if (build->builder->host) {
			xsnprintf(path1, sizeof path1, "logs/%s@%s/%s-%s_%s.tmp", build->builder->arch, build->builder->host->arch, name, version, revision);
			xsnprintf(path2, sizeof path2, "logs/%s@%s/%s-%s_%s.log", build->builder->arch, build->builder->host->arch, name, version, revision);
		} else {
			xsnprintf(path1, sizeof path1, "logs/%s/%s-%s_%s.tmp", build->builder->arch, name, version, revision);
			xsnprintf(path2, sizeof path2, "logs/%s/%s-%s_%s.log", build->builder->arch, name, version, revision);
		}
		if (rename(path1, path2) == -1) {
			fprintf(stderr, "rename: %s: %s\n", path1, strerror(errno));
			exit(1);
		}

		build->flags &= ~FLAG_DIRTY;
		pkgnamedone(build->pkgname, false);
		for (size_t i = 0; i < build->nsubpkgs; i++) {
			pkgnamedone(build->subpkgs[i], false);
		}
	}
}

static int
buildstart(struct job *j, struct build *build)
{
	extern char **environ;
	char path[PATH_MAX];
	posix_spawn_file_actions_t actions;
	char *Nargv[] = {NULL, "-1Et", "-j", "4", "pkg", build->pkgname->name, NULL};
	char *Xargv[] = {NULL, "-a", build->builder->arch, "-1Et", "-j", "4", "pkg", build->pkgname->name, NULL};
	char **argv;
	int fd;

	j->failed = false;
	j->build = build;
	j->status = 0;

	if (build->builder->host)
		xsnprintf(path, sizeof path, "logs/%s@%s/%s-%s_%s.tmp", build->builder->arch, build->builder->host->arch, build->pkgname->name, build->version, build->revision);
	else
		xsnprintf(path, sizeof path, "logs/%s/%s-%s_%s.tmp", build->builder->arch, build->pkgname->name, build->version, build->revision);
	fd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (fd == -1) {
		perror("open");
		exit(1);
	}

	if (build->builder->host)
		argv = Xargv;
	else
		argv = Nargv;
	xsnprintf(path, sizeof path, "%s/xbps-src", distdir);
	argv[0] = path;

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
		fprintf(stderr, "posix_spawn: %s: %s\n", build->pkgname->name, strerror(errno));
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
jobstart(struct job *j, struct build *build)
{
	if (build->flags & FLAG_DEPS) {
		return buildstart(j, build);
	} else {
		return gendepstart(j, build);
	}
}

static void
jobdone(struct job *j)
{
	numfinished++;
	if (WIFEXITED(j->status)) {
		; /* exit status is handled by builddone and gendepdone */
	} else if (WIFSIGNALED(j->status)) {
		fprintf(stderr, "job terminated due to signal %d: %s\n", WTERMSIG(j->status), j->build->pkgname->name);
		j->failed = true;
	} else {
		/* cannot happen according to POSIX */
		fprintf(stderr, "job status unknown: %s\n", j->build->pkgname->name);
		j->failed = true;
	}
	if (j->build->flags & FLAG_DEPS) {
		builddone(j);
	} else {
		gendepdone(j);
	}
}

static struct build *
mkbuild(struct pkgname *pkgname, struct builder *builder)
{
	struct build *build;
	build = xzmalloc(sizeof *build);
	build->builder = builder;
	build->pkgname = pkgname;
	build->allnext = builds;
	build->depmtime = MTIME_UNKNOWN;
	build->deperrmtime = MTIME_UNKNOWN;
	build->logmtime = MTIME_UNKNOWN;
	build->logerrmtime = MTIME_UNKNOWN;
	builds = build;
	pkgnamebuild(pkgname, build);
	return build;
}

static int
_buildadd(struct pkgname *pkgname, struct builder *builder)
{
	struct build *build = NULL;

	if (pkgname->mtime == MTIME_UNKNOWN) {
		pkgnamestat(pkgname);
		if (pkgname->mtime == MTIME_MISSING) {
			build->flags |= FLAG_SKIP|FLAG_DIRTY;
			if (explain)
				fprintf(stderr, "explain: %s: skipping, no template to build package\n", pkgname->name);
			goto out;
		}
	}
	
	struct pkgname *srcpkg = pkgname->srcpkg ? pkgname->srcpkg : pkgname;
	for (size_t i = 0; i < srcpkg->nbuilds; i++) {
		if (srcpkg->builds[i]->builder == builder) {
			build = srcpkg->builds[i];
			break;
		}
	}
	if (!build)
		build = mkbuild(srcpkg, builder);

	if (build->flags & FLAG_CYCLE) {
		build->flags |= FLAG_SKIP|FLAG_DIRTY;
		if (explain)
			fprintf(stderr, "explain: %s: skipping, dependency cycle involving: %s", pkgname->name, pkgname->name);
		goto err;
	}
	if (build->flags & FLAG_WORK)
		return 0;

	build->flags |= FLAG_CYCLE|FLAG_WORK;
	build->flags &= ~FLAG_DIRTY;

	/* build->pkgname->dirty = false; */
	/* if (build->pkgname->mtime == MTIME_UNKNOWN) */
	/* 	pkgnamestat(build->pkgname); */
	for (size_t i = 0; i < build->nsubpkgs; i++) {
		struct pkgname *n1 = build->subpkgs[i];
		/* build->pkgname->dirty = false; */
		/* if (n1->mtime == MTIME_UNKNOWN) */
		/* 	pkgnamestat(n1); */
	}

	if (build->depmtime == MTIME_UNKNOWN)
		depstat(build);

	/* dep file missing or outdated */
	if (build->depmtime < build->pkgname->mtime) {
		/* depfile error missing or older than template, regenerate it */
		if (build->deperrmtime < build->pkgname->mtime) {
			/* XXX: order is irrelevant, but would ordering still make sense
			 * to prioritize building packages over generating deps in
			 * case we have an old dep file? */
			if (explain)
				fprintf(stderr, "explain %s@%s: dependency file %s\n", build->pkgname->name, build->builder->arch,
				    build->depmtime == MTIME_MISSING ? "missing" : "older than template");
			build->flags |= FLAG_DIRTY;
			build->nblock = 0;
			goto out;
		} else {
			build->flags |= FLAG_SKIP|FLAG_DIRTY;
			if (explain)
				fprintf(stderr, "explain %s@%s: skipping, template unchanged since previous error\n", build->pkgname->name, build->builder->arch);
			goto out;
		}
	}

	loaddeps(build);
	if ((build->flags & FLAG_DEPS)) {
		logstat(build);
		if (build->logmtime == MTIME_MISSING) {
			if (build->logerrmtime == MTIME_MISSING) {
				/* Build the package if log and error mtime are missing */
				if (explain)
					fprintf(stderr, "explain %s@%s: missing\n", build->pkgname->name, build->builder->arch);
				build->flags |= FLAG_DIRTY;
			} else if (build->logerrmtime < build->pkgname->mtime) {
				/* Build the package if log mtime is missing and error mtime is older than the template */
				if (explain)
					fprintf(stderr, "explain %s@%s: reattempt, template changed since previous error\n", build->pkgname->name, build->builder->arch, build->pkgname->name);
				build->flags |= FLAG_DIRTY;
			} else {
				build->flags |= FLAG_SKIP|FLAG_DIRTY;
				if (explain)
					fprintf(stderr, "explain %s@%s: skipping, template unchanged since previous error\n", build->pkgname->name, build->builder->arch, build->pkgname->name);
				goto out;
			}
		}

		build->nblock = 0;
		struct builder *hostbuilder = builder->host ? builder->host : builder;
		for (size_t i = 0; i < build->nhostdeps; i++) {
			struct pkgname *n1 = build->hostdeps[i];
			int flags = _buildadd(n1, hostbuilder);
			if (flags & FLAG_CYCLE) {
				build->flags |= FLAG_SKIP|FLAG_DIRTY;
				fprintf(stderr, " <- %s", pkgname->name);
				goto err;
			}
			if (flags & FLAG_DIRTY)
				build->nblock++;
		}

		for (size_t i = 0; i < build->ntargetdeps; i++) {
			struct pkgname *n1 = build->targetdeps[i];
			int flags = _buildadd(n1, builder);
			if (flags & FLAG_CYCLE) {
				build->flags |= FLAG_SKIP|FLAG_DIRTY;
				fprintf(stderr, " <- %s", pkgname->name);
				goto err;
			}
			if (flags & FLAG_DIRTY)
				build->nblock++;
		}
	}

out:
	build->flags &= ~FLAG_CYCLE;
err:
	if (build->flags & FLAG_DIRTY) {
		/* Missing deps or missing package, mark all packages as dirty */
		build->pkgname->dirty = true;
		for (size_t i = 0; i < build->nsubpkgs; i++) {
			struct pkgname *n1 = build->subpkgs[i];
			n1->dirty = true;
		}

		if (!(build->flags & FLAG_SKIP)) {
			if (build->nblock == 0)
				queue(build);
			numtotal++;
		}
	}
	return build->flags;
}

static void
buildadd(struct pkgname *pkgname, struct builder *builder)
{
	int rv;
	if ((rv = _buildadd(pkgname, builder)) != 0) {
		if (rv == ELOOP) {
			fprintf(stderr, "\n");
			return;
		}
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
nextjob:
		while (work && numjobs < maxjobs) {
			struct build *build = work;
			work = work->worknext;
			if (dryrun) {
				numfinished++;
				fprintf(stderr, "[%zu/%zu] build %s\n", numfinished, numtotal, build->pkgname->name);
				pkgnamedone(build->pkgname, false);
				for (size_t i = 0; i < build->nsubpkgs; i++) {
					pkgnamedone(build->subpkgs[i], false);
				}
				continue;
			}

			if (jobstart(&jobs[next], build) == -1) {
				fprintf(stderr, "job failed to start: %s\n", build->pkgname->name);
				numfail++;
				continue;
			}
			const char *action = jobs[next].build->flags & FLAG_DEPS ? "build package" : "generated dependencies for";
			/* fprintf(stderr, "[%zu/%zu] %s %s pid=%zu\n", numfinished, numtotal, action, jobs[next].build->pkgname->name, jobs[next].pid); */
			next = jobs[next].next;
			numjobs++;
		}

		if (numjobs == 0)
			break;

		for (;;) {
			int status;
			pid_t pid = waitpid(-1, &status, 0);
			if (pid == -1) {
				perror("waitpid");
				exit(1);
			}

			for (size_t i = 0; i < maxjobs; i++) {
				if (jobs[i].pid != pid)
					continue;
				const char *action = jobs[i].build->flags & FLAG_DEPS ? "build package" : "generated dependencies for";
				jobs[i].status = status;
				jobdone(&jobs[i]);
				numjobs--;
				jobs[i].next = next;
				jobs[i].pid = -1;
				next = i;
				if (jobs[i].failed)
					numfail++;
				fprintf(stderr, "[%zu/%zu] %s %s\n", numfinished, numtotal, action, jobs[i].build->pkgname->name);
				goto nextjob;
			}
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
		struct pkgname *pkgname = mkpkgname(ent->d_name);
	}
	closedir(dp);
	close(dirfd);
}

static int
mkpath(const char *path, mode_t mode)
{
	char tmp[PATH_MAX];
	char *slash = tmp;
	bool done = false;
	size_t l = strlcpy(tmp, path, sizeof tmp);
	if (l >= sizeof tmp) {
		errno = ENOBUFS;
		return -1;
	}
	while (!done) {
		slash += strspn(slash, "/");
		slash += strcspn(slash, "/");
		done = (*slash == '\0');
		*slash = '\0';
		if (mkdir(tmp, mode) == -1) {
			if (errno != EEXIST)
				return -1;
		}
		*slash = '/';
	}
}

int
main(int argc, char *argv[])
{
	char path[PATH_MAX];
	int c;
	unsigned long ul;
	const char *tool = NULL;
	struct builder *builder, *tmpbuilder;

	while ((c = getopt(argc, argv, "dD:j:nt:")) != -1)
		switch (c) {
		case 'd':
			explain = true;
			break;
		case 'D':
			distdir = optarg;
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
		case 't':
			tool = optarg;
			break;
		default:
			fprintf(stderr, "usage: %s [-den] [-D distdir] [-j jobs] [target...]\n", *argv);
		}

	argc -= optind;
	argv += optind;

	struct builder *host = mkbuilder("x86_64");
	struct builder *cross = mkbuilder("aarch64");
	cross->host = host;

	if (!distdir) {
		static char defdistdir[PATH_MAX];
		const char *home;
		if (!(home = getenv("HOME"))) {
			fprintf(stderr, "getenv: HOME: not defined\n");
			exit(1);
		}
		xsnprintf(defdistdir, sizeof defdistdir, "%s/void-packages", home);
		distdir = defdistdir;
	}

	/* setup the state directories */
	HASH_ITER(hh, builders, builder, tmpbuilder) {
		if (builder->host)
			xsnprintf(path, sizeof path, "logs/%s@%s", builder->arch, builder->host->arch);
		else
			xsnprintf(path, sizeof path, "logs/%s", builder->arch);
		if (mkpath(path, 0755) == -1) {
			fprintf(stderr, "mkpath: %s: %s\n", path, strerror(errno));
			exit(1);
		}
		if (builder->host)
			xsnprintf(path, sizeof path, "deps/%s@%s", builder->arch, builder->host->arch);
		else
			xsnprintf(path, sizeof path, "deps/%s", builder->arch);
		if (mkpath(path, 0755) == -1) {
			fprintf(stderr, "mkpath: %s: %s\n", path, strerror(errno));
			exit(1);
		}
	}

	if (argc > 0) {
		for (int i = 0; i < argc; i++) {
			/* buildadd(mkpkgname(argv[i]), host); */
			buildadd(mkpkgname(argv[i]), cross);
		}
	} else {
		struct pkgname *pkgname, *tmp;
		scan();
		/* build all packages */
		HASH_ITER(hh, pkgnames, pkgname, tmp) {
			/* buildadd(pkgname, host); */
			buildadd(pkgname, cross);
		}
	}

	if (!tool)
		build();
	return 0;
}
