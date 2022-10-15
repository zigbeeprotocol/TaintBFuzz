#include <stdarg.h>

/*@ requires n>= 0;
  @ ensures \result >=0; */
int sum(int n, ...);

int main(){
  return sum(5, 6, 9, 14, 12, 1);
}


int sum(int n, ...){
  int ret = 0;
  int i = 0;
  va_list args;
  va_start(args, n);

  for(i; i<n; i++){
    ret += va_arg(args, int);
  }

  va_end(args);
  return ret;
}
