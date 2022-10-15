/* run.config
 MODULE: @PTEST_NAME@
   OPT: -kernel-warn-key transient-block=active
*/

void f(void) { }

int main () {

  int x = 1;
  x = 2;
  f();

}
