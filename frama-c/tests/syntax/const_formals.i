const char* s = "foo";
char mutable_s[] = "bar";
const char**p = &s;

char f(const char* s) { return s[0]; }

char g(const char* const* a) { return **a; }

// we ignore restrict differences. GCC and Clang do that too
void foo(int *restrict x, int* y);
void foo(int *x, int* restrict y) { *x++; *y--; }

// play a little bit with function pointers.
int incr_get(int* x) { *x++; return *x; }

int get(const int*x) { return *x; }

int apply_const(int* x, int (*g)(const int*y)) {
  return g(x);
}

int apply_non_const (int* x, int(*g)(int*y)) {
  return g(x);
}

int main() {
  int x = 1;
  apply_const(&x,incr_get); // should warn
  apply_non_const(&x,incr_get); // ok
  apply_const(&x,get); // ok
  apply_non_const(&x,get); // ok
  char c = f(mutable_s); // implicit conversion should not raise warning
  char d = g(p); // implicit conversion should not raise warning
}
