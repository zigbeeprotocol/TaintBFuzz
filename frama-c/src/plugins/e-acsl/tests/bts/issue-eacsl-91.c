/* run.config
   COMMENT: frama-c/e-acsl#91, test for misplaced delete_block of local variable
   in switch.
   STDOPT: #"-e-acsl-full-mtracking"
*/
short a;
char b() {
  switch (a) {
    int c = 0;
  case 0:
    goto d;
    /* Empty if statement so that frama-c simplifies this in `int tmp = c;` */
    if (c)
      ;
  }
d:
  return 2;
}

int main() {
  b();
  return 0;
}
