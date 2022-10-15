/* run.config
   STDOPT:
   STDOPT: #"-nonterm-dead-code"
 */

volatile int nondet;

int loop() {
  int i = 0;
 loop:
  if (nondet) goto loop;
  else goto loop1;
  i+=2;
 loop1:
  i++;
  goto loop;
  return 3;
}

int loop2() {
 loop:
  switch (nondet) {
  case 1: goto loop;
  case 2: goto loop;
  default: goto loop;
  }
}

int loop3() {
 loop:
  if (nondet) goto loop; else goto loop;
}

int main2() {
  if (nondet) loop();
  else nondet ? loop2() : loop3();
  return 0;
}

int main() {
  while (1)
    main2();
}
