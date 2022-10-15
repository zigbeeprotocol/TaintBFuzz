#include <limits.h>

int main(int argc, char *argv[]) {
  /*@ assert \exists unsigned int x; -1 < x < 5 && x == 0;*/
  /*@ assert !(\forall unsigned int x; -1 < x < 5 ==> x != 0);*/
  return 0;
}
