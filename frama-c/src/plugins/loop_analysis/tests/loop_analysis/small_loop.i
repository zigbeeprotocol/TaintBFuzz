volatile int nondet;
int main() {
  int i;
  int s = 0;
  for (i = 0; i < 10; i++) {
    if (nondet) {
      s++;
    }
    s++;
  }
  return 0;
}
