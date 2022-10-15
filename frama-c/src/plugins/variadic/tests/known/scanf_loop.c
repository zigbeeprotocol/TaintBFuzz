#include <stdio.h>
volatile int nondet;
int main (void)
{
  int n;
  while (scanf ("%d", &n) > 0) {
    if (nondet) break;
  }
  return n;
}
