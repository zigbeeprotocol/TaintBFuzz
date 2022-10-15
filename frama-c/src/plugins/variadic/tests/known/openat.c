#include <fcntl.h>

int main(){
  int flag = 0;
  mode_t mode1 = 0;
  int mode2 = 0;
  char* file = "file";
  openat(0, file, flag, mode1);
  openat(0, file, flag, mode2);
  openat(0, file, flag, 3.0);
  return 0;
}
