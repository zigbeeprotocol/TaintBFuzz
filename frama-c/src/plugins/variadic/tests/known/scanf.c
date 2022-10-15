#include <stdio.h>

int main(){
  char c[10];
  int i;

  scanf("Hello %*10le %% %10s %[^]world] %d !", c, c, &i);
}
