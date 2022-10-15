/* run.config
   EXECNOW: LOG save_load.sav.res LOG save_load.sav.err BIN @PTEST_NAME@.sav @frama-c@ -wp-warn-key pedantic-assigns=inactive -wp-share @PTEST_SHARE_DIR@ -wp -wp-print -wp-prover none @PTEST_FILE@ -save @PTEST_RESULT@/@PTEST_NAME@.sav > @PTEST_RESULT@/@PTEST_NAME@.sav.res 2> @PTEST_RESULT@/@PTEST_NAME@.sav.err
   CMD: @frama-c@ -load %{dep:@PTEST_RESULT@/@PTEST_NAME@.sav} -wp-warn-key pedantic-assigns=inactive
   OPT: -print
   OPT: -wp -wp-prover none -wp-print
*/

/* run.config_qualif
   DONTRUN:
*/

// Unprovable contract, just here to check the WP generation.
// The test case 1 checks that save/load do not crash in presence of WP.
// The test case 2 checks that WP still works after save/load.

//@ ensures (a+b) > 0 ;
int f(int a,int b,int c) {
  if (c) a++; else b--;
  return a+b;
}
