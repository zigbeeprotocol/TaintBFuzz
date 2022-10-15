#include <fcntl.h>

int main(){
  int flag = 0;
  int mode = 0;
  char* file = "file";
  int fd1 = open(file, flag, mode);
  int fd2 = open(file, flag);
  int fd3 = open(file, flag, mode, 3, "arg4", 5);
  return 0;
}
