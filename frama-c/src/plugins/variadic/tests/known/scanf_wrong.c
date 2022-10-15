#include <stdio.h>

int main(){
  double d;
  char c[10];
  int i;

  scanf("Hello %*10le %% %10s %[^]world] %d !", d, c, &i);
}
