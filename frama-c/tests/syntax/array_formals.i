int f(int a[2]) { return a[1]; }

int g(int a[static 2]) { return a[1]; }

int h(int a[static restrict const 2]) { return a[1]; }

typedef int (__attribute__((test)) arr)[2];

int k(arr a) { return a[1]; }

int l() {
  arr a = { 0 };
  return k(a);
}
