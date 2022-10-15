#include <stropts.h>

struct st {
  int a;
};

int main(){
  int fd1 = 1;
  int request1 = 0;
  // From POSIX: "The type of arg depends upon the particular control request,
  //              but it shall be either an integer or a pointer to a
  //              device-specific data structure."
  int r1 = ioctl(fd1, request1); // without 3rd argument
  char arg = 42;
  int r2 = ioctl(fd1, request1, &arg); // with 3rd argument
  struct st *p = 0;
  ioctl(fd1, request1, p); // with 3rd argument that is a null pointer
  ioctl(fd1, request1, 42); // with 3rd argument that is an integer
  return 0;
}
