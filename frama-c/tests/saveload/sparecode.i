/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
 PLUGIN: @EVA_PLUGINS@ slicing
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -slicing-level 2 -slice-return main -eva-show-progress -save @PTEST_NAME@.sav @PTEST_FILE@ -then-on 'Slicing export' -print > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}"
*/
int G;
int f (int x, int y) {
  G = y;
  return x;
}

int main (void) {
  int a = 1;
  int b = 1;

  f (0, 0); /* this call is useless : should be removed */
  a = f (a, b); /* the result of this call is useless */
  a = f (G + 1, b);

  G = 0; /* don't use the G computed by f */

  return a;
}
