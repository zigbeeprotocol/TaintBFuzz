// possibly non-terminating program => not reported

volatile int nondet;

int main() {
 loop:
  if (nondet) goto loop;
  return 0;
}
