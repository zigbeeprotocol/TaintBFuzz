/* run.config
   COMMENT: test option -e-acsl-functions
   STDOPT: #"-e-acsl-functions f"
*/
/* run.config_dev
   MACRO: ROOT_EACSL_GCC_FC_EXTRA_EXT -e-acsl-functions f
*/

/*@ requires \initialized(p);
  @ requires *p == 0;
  @ ensures \result == \old(*p); */
int f(int *p) {
  /*@ loop invariant 0 <= i <= 1; */
  for (int i = 0; i < 1; i++)
    ;
  return 0;
}

/*@ requires \initialized(p);
  @ requires *p == 1;
  @ ensures \result == \old(*p); */
int g(int *p) {
  /*@ loop invariant 0 <= i <= 1; */
  for (int i = 0; i < 1; i++)
    ;
  return 0;
}

int main(void) {
  int x = 0;
  int y = 0;
  f(&x);
  // Here we test that E-ACSL only checks function f() at runtime, so the
  // precondition *p == 1 of g() is invalid on purpose. If the option is not
  // working correctly, the runtime test will fail.
  // Eva correctly identifies the property as invalid and displays a message in
  // the test oracle.
  g(&y);
}
