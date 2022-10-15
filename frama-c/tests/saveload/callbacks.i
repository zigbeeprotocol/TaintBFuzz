/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ @PTEST_FILE@ -out -calldeps -eva-show-progress -main main1 -save @PTEST_NAME@.sav > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav} -main main2 -then -main main3"
*/

/* This tests whether the callbacks for callwise inout and from survive after
   a saveload or a -then */

void f(int *p) {
  *p = 1;
}

int x, y;

void g1() {
  f(&x);
}


void g2() {
  f(&y);
}

void main1() {
  g1();
  g2();
}

void main2() {
  g1();
  g2();
}

void main3() {
  g1();
  g2();
}
