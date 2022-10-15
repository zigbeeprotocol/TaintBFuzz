#include <string.h>
#include <stdio.h>

volatile int nondet;

int main() {
  char data[100];
  memset(data, 'A', 99);
  data[99] = 0;
  char dest[50] = "";
  if (nondet) {
    snprintf(dest, strlen(data), "%s", data); // must fail
    //@ assert \false;
  }
  snprintf(dest, strlen(data)/2, "%s", data); // ok
  return 0;
}
