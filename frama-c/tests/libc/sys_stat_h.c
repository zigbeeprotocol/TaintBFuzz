/*run.config
  STDOPT: #"-eva-slevel 2"
*/
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

volatile int nondet;
int main() {
  int fd = open("/tmp/bla", O_RDWR, S_IRWXU | S_IRWXG);
  if (fd == -1) return 1;
  if (close(fd)) return 2;
  struct stat st;
  int r = stat("/tmp/bla", &st);
  if (r) return r;
  if (st.st_size <= 0) return 3;
  int r_mkdir = mkdir("/tmp/tmp", 0755);
  if (nondet) {
    char non_terminated[7] = "invalid";
    mkdir(non_terminated, 0422);
  }
  mode_t old_mask = umask(0644);
  int r2 = lstat("/tmp/bla", &st);
  int r3 = mkfifo("/tmp/fifo", 0644);
  int r4 = mknod("/tmp/fifo2", 0644, 42);

  int r5 = chmod("/tmp/bla", 0700);

  int r6 = fchmod(fd, 0700);

  int r7 = fchmodat(AT_FDCWD, "bla", 0700, AT_SYMLINK_NOFOLLOW);

  struct stat buf;

  int r8 = fstat(fd, &buf);

  int r9 = fstatat(AT_FDCWD, "bla", &buf, AT_SYMLINK_NOFOLLOW);

  return 0;
}
