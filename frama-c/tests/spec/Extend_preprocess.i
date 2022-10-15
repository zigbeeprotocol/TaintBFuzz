/* run.config
MODULE: @PTEST_NAME@
OPT: -no-autoload-plugins -kernel-warn-key=annot-error=active -print
*/

/*@ bhv_foo must_replace(x); */
int f(int x);

/*@ behavior test:
  bhv_foo must_replace(x);
*/
int g(int x);


int f(int x) {
  int s = 0;
  /*@ loop nl_foo must_replace(x); */
  for (int i = 0; i < x; i++) s+=g(i);
  /*@ ca_foo must_replace(x); */
  return s;
}

int k(int z) {
  int x = z;
  int y = 0;
  /*@ ns_foo must_replace(x); */
  y = x++;
  return y;
}

/*@ gl_foo must_replace(x); */
