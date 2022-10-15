#include <sys/sendfile.h>
#include <fcntl.h>
#include <unistd.h>

int main() {
  int out_fd, in_fd;
  in_fd = open("/tmp/in.txt", O_RDONLY);
  if (in_fd == -1) return 1;
  out_fd = open("/tmp/out.txt", O_CREAT, O_WRONLY);
  if (out_fd == -1) return 1;
  off_t offset = 0;
  ssize_t r1, r2, r3;
  r1 = sendfile(out_fd, in_fd, &offset, 42);
  //@ assert -1 <= r1 <= 42;
  int r = close(out_fd);
  if (r) return 1;
  out_fd = open("/tmp/out.txt", O_CREAT, O_WRONLY);
  if (out_fd == -1) return 1;
  r3 = sendfile(out_fd, in_fd, 0, 42);
  close(out_fd);
  close(in_fd);
  return 0;
}
