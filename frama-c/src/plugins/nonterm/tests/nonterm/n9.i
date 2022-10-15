volatile int nondet;

int f() {
  int i;
  int res = 0;
  i = 0;
  while (i < 10) {
    res += i;
    i--;
    i++;
  }
  return 0;
}

int g() {
  int i;
  int res = 0;
  i = 0;
  while (i < 10)
    res +=
      i;
  return 0;
}

int f_explicit_break() {
  int i;
  int res = 0;
  i = 0;
  while (1) {
    if (i >= 10) break;
    res += i;
    i--;
    i++;
  }
  return 0;
}

int main() {
  int i;
  int res = 0;
  if (nondet) f();
  if (nondet) g();
  if (nondet) f_explicit_break();
  return 0;
}
