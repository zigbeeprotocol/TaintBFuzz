#include <sys/uio.h>
#include <unistd.h>
#include <fcntl.h>
volatile int nondet;
int main() {
  char *str = "A small string";
  char *empty_buf = 0;
  char buf[10] = "\n\n\nbuffer";
  char buf2[14];
  struct iovec v[4] =
    {
     {str, 15},
     {empty_buf, 0},
     {buf, 10},
     {buf2, 14},
    };
  int fd = open("/tmp/uio.txt", O_WRONLY | O_CREAT, 0660);
  if (fd < 0) return 1;
  //@ assert \valid_read(((char*)v[0].iov_base) + (0 .. v[0].iov_len-1));
  //@ assert \valid_read(((char*)v[1].iov_base) + (0 .. v[1].iov_len-1));
  //@ assert \valid_read(((char*)v[2].iov_base) + (0 .. v[2].iov_len-1));
  ssize_t w = writev(fd, v, 3);
  close(fd);
  fd = open("/tmp/uio.txt", O_RDONLY);
  ssize_t r = readv(fd, v+2, 2);
  close(fd);

  if (nondet) {
    char buf3[10] = "\n\n\nbuffer";
    char buf4[14];
    struct iovec v2[4] =
      {
        {str, 15},
        {empty_buf, 0},
        {buf3, 11}, // invalid length
      };
    int fd2 = open("/tmp/uio2.txt", O_WRONLY | O_CREAT, 0660);
    if (fd2 < 0) return 1;
    ssize_t w = writev(fd2, v2, 3); // must fail
    //@ assert unreachable: \false;
  }

  return w + r;
}
