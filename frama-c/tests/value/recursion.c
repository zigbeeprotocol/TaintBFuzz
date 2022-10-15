/* run.config_apron,run.config_multidim
   DONTRUN: The Apron and multidim domains do not support recursion.
*/
/* run.config*
   STDOPT: +"-eva-no-show-progress -eva-unroll-recursive-calls 0"
   STDOPT: +"-eva-no-show-progress -eva-unroll-recursive-calls 20"
   EXIT: 1
   STDOPT: +"-eva-no-show-progress -eva-unroll-recursive-calls 5 -main main_fail"
*/

#include <__fc_builtin.h>

volatile int nondet;

/* ----- Simple recursive functions. ---------------------------------------- */

/*@ assigns \result \from \nothing;
    ensures \result == 5; */
int five () {
  if (nondet)
    return five();
  else
    return 5;
}

/*@ assigns \result \from i;
    ensures \result == (i * (i+1)) / 2; */
unsigned int sum (unsigned int i) {
  if (i < 2)
    return i;
  unsigned int res = i + sum(i - 1);
  return res;
}

/*@ assigns \result \from i; */
unsigned int factorial (unsigned int i) {
  if(i <= 1) {
    return 1;
  }
  unsigned int res = i * factorial(i - 1);
  return res;
}

/*@ assigns \result \from i, n; */
unsigned int syracuse (unsigned int n, unsigned int i) {
  if (i == 0)
    return n;
  else {
    unsigned int prev = syracuse(n, i-1);
    if (prev % 2)
      return 3*prev + 1;
    else
      return prev / 2;
  }
}

/*@ assigns \result \from n; */
unsigned int fibonacci (unsigned int n) {
  if (n < 2)
    return n;
  else {
    unsigned int x = fibonacci(n-1);
    unsigned int y = fibonacci(n-2);
    return x + y;
  }
}

/* ----- Recursive functions using pointers on the stack. ------------------ */

/*@ assigns *result \from *p;
    ensures \initialized(result);
    ensures *result == (*p * (*p+1)) / 2; */
void sum_ptr (unsigned int *p, unsigned int *result) {
  if (*p < 2)
    *result = *p;
  else {
    unsigned int res;
    unsigned int arg = *p - 1;
    sum_ptr(&arg, &res);
    *result = *p + res;
  }
}

/*@ assigns *result \from *p; */
void factorial_ptr(unsigned int *p, unsigned int *result) {
  if(*p < 2) {
    *result = 1;
  }
  else {
    unsigned int res;
    unsigned int arg = *p - 1;
    factorial_ptr(&arg, &res);
    *result = *p * res;
  }
}

/*@ assigns *result \from n, *p; */
void syracuse_ptr (unsigned int n, unsigned int *p, unsigned int *result) {
  if (*p == 0)
    *result = n;
  else {
    unsigned int prev_res;
    unsigned int prev_arg = *p - 1;
    syracuse_ptr(n, &prev_arg, &prev_res);
    if (prev_res % 2)
      *result = 3*prev_res + 1;
    else
      *result = prev_res / 2;
  }
}

/*@ assigns *result \from *p; */
void fibonacci_ptr (unsigned int *p, unsigned int *result) {
  if (*p < 2)
    *result = *p;
  else {
    unsigned int x, y;
    unsigned int a = *p;
    a--;
    fibonacci_ptr(&a, &x);
    a--;
    fibonacci_ptr(&a, &y);
    *result = x + y;
  }
}

/* ----- Recursive functions performing several computations at once. ------- */

/*@ assigns \result \from i;
    assigns *sum \from i;
    ensures \initialized(sum);
    ensures *sum == (i * (i+1)) / 2; */
unsigned int sum_and_fact (unsigned int i, unsigned int *sum) {
  if (i < 2) {
    *sum = i;
    return i;
  }
  else {
    unsigned int tmp;
    unsigned int fact = i * sum_and_fact(i-1, &tmp);
    *sum = i + tmp;
    return fact;
  }
}

/* ----- Mutually recursive functions. -------------------------------------- */

int even (unsigned int);
void even_ptr (unsigned int, int*);

/*@ assigns \result \from n;
    ensures \result == n % 2; */
int odd (unsigned int n) {
  if (n)
    return even(n-1);
  else
    return 0;
}

/*@ assigns \result \from n;
    ensures \result == !(n % 2); */
int even (unsigned int n) {
  if (n)
    return odd(n-1);
  else
    return 1;
}

/*@ assigns *result \from n;
    ensures *result == n % 2; */
void odd_ptr (unsigned int n, int *result) {
  if (n) {
    int x;
    even_ptr(n-1, &x);
    *result = x;
  }
  else
    *result = 0;
}

/*@ assigns *result \from n;
    ensures *result == !(n % 2); */
void even_ptr (unsigned int n, int *result) {
  if (n) {
    int y;
    odd_ptr(n-1, &y);
    *result = y;
  }
  else
    *result = 1;
}

/* ----- Recursive functions on arrays. ------------------------------------- */

/*@ requires \valid(&data[start..end]);
    assigns data[start..end] \from start;
    ensures \initialized(&data[start..end]); */
void fill_array (int *data, int start, int end) {
  if (start < 0 || start > end)
    return;
  else {
    data[start] = start;
    fill_array(data, start + 1, end);
  }
}

/*@ requires \valid_read(&data[start..end]);
    requires \initialized(&data[start..end]);
    assigns \result \from data[start..end], toFind; */
int binary_search (int *data, int toFind, int start, int end) {
  int mid = start + (end - start)/2;
  if (start > end)
    return -1;
  else if (data[mid] == toFind)
    return mid;
  else if (data[mid] > toFind)
    return binary_search(data, toFind, start, mid-1);
  else
    return binary_search(data, toFind, mid+1, end);
}

void test_array () {
  int array[16], i, j, end;
  if (nondet) {
    fill_array(array, 0, 16);
    Frama_C_show_each_unreachable(array);
  }
  end = Frama_C_interval(10, 16);
  fill_array(array, 0, end);

  i = binary_search(array, 3, 0, 15);
  Frama_C_show_each_3(i);
  i = binary_search(array, 12, 0, 15);
  Frama_C_show_each_12(i);
  i = binary_search(array, 20, 0, 15);
  Frama_C_show_each_minus1(i);

  fill_array(array, 10, 15);
  j = Frama_C_interval(7, 11);
  i = binary_search(array, j, 0, 15);
  Frama_C_show_each_7_11(i);
  j = Frama_C_interval(7, 18);
  i = binary_search(array, j, 0, 15);
  Frama_C_show_each_minus_1_15(i);
}

/* ----- Alarms or invalid preconditions in recursive calls. ---------------- */

/*@ assigns \result \from i;
    ensures \result > 0; */
int alarm (int i) {
  if(i <= 1) {
    return 1;
  }
  int res = i * alarm(i - 1); // alarm if enough recursive calls are made.
  return res;
}

/* The precondition should become invalid if enough recursive calls are made. */
/*@ requires x != 16;
    assigns \nothing; */
void precond (int x) {
  int y = 100 / (x - 16);
  if (nondet)
    precond(x+1);
}

/* ----- Variables escaping scope through recursive function. --------------- */

int *p;

/*@ assigns p \from \nothing;
    assigns *p \from \nothing; */
void escaping_local (int count) {
  if (count <= 0)
    return;
  else {
    int x;
    p = &x;
    escaping_local(count - 1);
    if (nondet) {
      *p = 17; // invalid, except the penultimate recursive call where count = 1
      Frama_C_show_each_1(count);
    }
  }
}

/*@ assigns p \from \nothing;
    assigns *p \from \nothing; */
void escaping_formal (int count, int x) {
  if (count <= 0)
    return;
  else {
    p = &x;
    escaping_formal(count - 1, x);
    if (nondet) {
      *p = 16; // invalid, except the penultimate recursive call where count = 1
      Frama_C_show_each_1(count);
    }
  }
}

/*@ assigns p \from q;
    assigns *p \from \nothing; */
void escaping_stack (int count, int *q) {
  if (count <= 0)
    return;
  else {
    int x;
    p = q;
    escaping_stack(count - 1, &x);
    if (nondet) {
      *p = 15;
      Frama_C_show_each_1_2(count);
    }
  }
}

/* ----- Bug with memexec. -------------------------------------------------- */

/*@ assigns \nothing;  */
void decr (int i) {
  if (nondet)
    return;
  else {
    int x = 100 / i; // alarm if i = 0.
    decr(i-1);
  }
}

void bug_memexec () {
  decr(25);
  /* Should trigger the alarm with -eva-unroll-recursive-calls 20, except that
     the memexec cache use the results of the previous call to not reinterpret
     the call. */
  decr(15);
}

/* ----- Main. -------------------------------------------------------------- */

void main () {
  int a, b;
  unsigned int x, y;
  /* Simple recursive functions. */
  a = five();
  Frama_C_show_each_5(a);
  y = sum(13);
  Frama_C_show_each_91(y);
  y = factorial(5);
  Frama_C_show_each_120(y);
  y = syracuse(12, 9);
  Frama_C_show_each_1(y);
  y = fibonacci(11);
  Frama_C_show_each_89(y);

  /* Recursive functions using pointers on the stack. */
  x = 13;
  sum_ptr(&x, &y);
  Frama_C_show_each_91(y);
  x = 5;
  factorial_ptr(&x, &y);
  Frama_C_show_each_120(y);
  x = 9;
  syracuse_ptr(12, &x, &y);
  Frama_C_show_each_1(y);
  x = 11;
  fibonacci_ptr(&x, &y);
  Frama_C_show_each_89(y);

  /* Recursive functions performing several computations at once. */
  y = sum_and_fact(8, &x);
  Frama_C_show_each_36_40320(x, y);

  /* Mutually recursive functions. */
  a = odd(7);
  b = even(8);
  Frama_C_show_each_1(a, b);
  a = odd(8);
  b = even(9);
  Frama_C_show_each_0(a, b);
  odd_ptr(7, &a);
  even_ptr(8, &b);
  Frama_C_show_each_1(a, b);
  odd_ptr(8, &a);
  even_ptr(9, &b);
  Frama_C_show_each_0(a, b);

  /* Using intervals. */

  x = Frama_C_interval(3, 11);
  y = sum(x);
  Frama_C_show_each_6_66(y);
  y = 0;
  sum_ptr(&x, &y);
  Frama_C_show_each_6_66(y);
  y = 0;
  y = fibonacci(x);
  Frama_C_show_each_2_89(y);
  y = 0;
  fibonacci_ptr(&x, &y);
  Frama_C_show_each_2_89(y);

  /* Misc */
  test_array();

  x = Frama_C_interval(10, 20);
  y = alarm(x);
  if (nondet) {
    y = alarm(20);
    Frama_C_show_each_unreachable(y);
  }
  precond(1);

  escaping_local(5);
  escaping_formal(5, 5);
  escaping_stack(5, &a);

  bug_memexec();
}

/* ----- Recursive function without specification. -------------------------- */

unsigned int sum_nospec (unsigned int i) {
  if (i < 2)
    return i;
  unsigned int res = i + sum_nospec(i - 1);
  return res;
}

void main_fail () {
  int x, y;
  y = sum_nospec(4);
  Frama_C_show_each_10(y);
  /* This call don't fail, as only 4 unrolling of [sum_nospec] are needed before
     using the results from the first call stored in the memexec cache. However,
     this call would fail without the first call to [sum_no_spec]. */
  y = sum_nospec(8);
  Frama_C_show_each_36(y);
  x = Frama_C_interval(4, 16);
  /* This call cannot be interpreted without a specification for [sum_nospec]. */
  y = sum_nospec(x);
  Frama_C_show_each_unreachable(y);
}
