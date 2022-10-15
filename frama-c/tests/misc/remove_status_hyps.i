/* run.config
 MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

int main(void) {
  /*@ assert P1: \true; */;
  /*@ assert P2: \true; */;
  /*@ assert P3: \true; */;
  /*@ assert P4: \true; */;
  return 0;
}
