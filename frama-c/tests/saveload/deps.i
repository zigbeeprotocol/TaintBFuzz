/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
 MODULE: deps_A
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -eva @EVA_OPTIONS@ -out -input -deps @PTEST_FILE@ -save @PTEST_NAME@.sav > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav} -eva @EVA_OPTIONS@ -out -input -deps "
 MODULE: deps_B
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}  -out -input -deps "
 MODULE: deps_C
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}  -out -input -deps "
 MODULE: deps_D
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}  -out -input -deps "
 MODULE: deps_E
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}  -out -input -deps "
*/

int main() {
  int i, j;

  i = 10;
  while(i--);
  j = 5;

  return 0;
}
