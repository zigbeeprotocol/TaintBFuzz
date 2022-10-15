/* run.config
 PLUGIN: @EVA_PLUGINS@
 MODULE: @PTEST_NAME@
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ @PTEST_FILE@ -save @PTEST_NAME@.sav > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
 MODULE:
 COMMENT: the CMD line below omits @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
   OPT: -load %{dep:@PTEST_NAME@.sav} -eva -eva-verbose 0
*/
int main() {
  return 0;
}
