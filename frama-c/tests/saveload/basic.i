/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
 MODULE: @PTEST_NAME@
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -eva @EVA_OPTIONS@ -out -input -deps @PTEST_FILE@ -save @PTEST_NAME@.sav > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
 MODULE:
   EXECNOW: BIN @PTEST_NAME@.1.sav LOG @PTEST_NAME@_sav.1.res LOG @PTEST_NAME@_sav.1.err @frama-c@ -save @PTEST_NAME@.1.sav @PTEST_FILE@ -eva @EVA_OPTIONS@ -out -input -deps > @PTEST_NAME@_sav.1.res 2> @PTEST_NAME@_sav.1.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav} -eva @EVA_OPTIONS@ -out -input -deps"
 MODULE: @PTEST_NAME@
   STDOPT: +"-load %{dep:@PTEST_NAME@.1.sav} -eva @EVA_OPTIONS@ -out -input -deps -print"
 MODULE:
   STDOPT: +"-load %{dep:@PTEST_NAME@.1.sav} -eva @EVA_OPTIONS@ -out -input -deps"
 MODULE: status
   EXECNOW: LOG status_sav.res LOG status_sav.err BIN status.sav @frama-c@ -save status.sav @PTEST_FILE@ > status_sav.res 2> status_sav.err
   STDOPT: +"-load %{dep:status.sav}"
 MODULE:
   STDOPT: +"-load %{dep:status.sav}"
*/
int main() {
  int i,j; i=10; /*@ assert (i == 10); */
  while(i--);
  j = 5;

  return 0;
}
