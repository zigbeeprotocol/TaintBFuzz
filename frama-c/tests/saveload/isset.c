/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -quiet -eva @EVA_OPTIONS@ -save @PTEST_NAME@.sav @PTEST_FILE@ > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-quiet -load %{dep:@PTEST_NAME@.sav}"
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}"
   STDOPT: +"-eva @EVA_OPTIONS@ -load %{dep:@PTEST_NAME@.sav}"
   STDOPT: +"-quiet -eva @EVA_OPTIONS@ -load %{dep:@PTEST_NAME@.sav}"
*/

int main() {
  int i, j;

  i = 10;
  while(i--);
  j = 5;

  return 0;
}
