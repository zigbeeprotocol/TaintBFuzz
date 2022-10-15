/* run.config
   STDOPT: +"-eva-unroll-recursive-calls 10 -eva-slevel 7"
 */

#include <stddef.h>

// Test that the last iteration of the variant can be negative
int f(int x) {
  /*@ loop variant x; */
  while (x >= 0) {
    x -= 2;
  }
  return x;
}

// Test variant with general measure
/*@ predicate lexico(integer x, integer y) =
      x > y && 0 <= x; */
int g(int x) {
  /*@ loop variant x for lexico; */
  while (x >= 0) {
    x -= 2;
  }
  return x;
}

// Test classic variant
/*@ requires n <= 12; */
int fact(int n) {
  int result = n;
  /*@ loop invariant n >= 1;
      loop variant n; */
  while (n > 1) {
    result *= (n - 1);
    --n;
  }
  return result;
}

// Test GMP variant
/*@ requires n <= 20; */
size_t fact2(size_t n) {
  size_t result = n;
  /*@ loop invariant 1 <= i < n;
      loop variant n - i; */
  for (size_t i = 1UL; i < (n - 1UL); i++) {
    result *= (n - i);
  }
  return result;
}

// Test decreases on recursive function
/*@ decreases n; */
int fib(int n) {
  if (n == 1)
    return 1;
  if (n <= 0)
    return 0;
  return fib(n - 1) + fib(n - 2);
}

// Test decreases on mutually recursive functions
int odd(int);
/*@ requires n >= 0;
    decreases n; */
int even(int n) {
  if (n == 0)
    return 1;
  return odd(n - 1);
}
/*@ requires n >= 0;
    decreases n; */
int odd(int n) {
  if (n == 0)
    return 0;
  return even(n - 1);
}

int main() {
  int f10 = f(10);
  //@ assert f10 == -2;
  int f7 = f(7);
  //@ assert f7 == -1;
  int g10 = g(10);
  //@ assert g10 == -2;
  int g7 = g(7);
  //@ assert g7 == -1;

  int fact7 = fact(7);
  //@ assert fact7 == 5040;

  size_t fact18 = fact2(18);
  //@ assert fact18 == 6402373705728000UL;

  int fib7 = fib(7);
  //@ assert fib7 == 13;

  int even7 = even(7);
  //@ assert even7 == 0;
  int even10 = even(10);
  //@ assert even10 == 1;
  int odd7 = odd(7);
  //@ assert odd7 == 1;
  int odd10 = odd(10);
  //@ assert odd10 == 0;

  return 0;
}
