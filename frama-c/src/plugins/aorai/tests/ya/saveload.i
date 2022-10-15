/* run.config
NOFRAMAC:
LIBS:
EXECNOW: LOG @PTEST_NAME@.res.0.log.txt BIN @PTEST_NAME@.sav @frama-c@ -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} @PTEST_FILE@ -save @PTEST_RESULT@/@PTEST_NAME@.sav > @PTEST_RESULT@/@PTEST_NAME@.res.0.log.txt
EXECNOW: LOG @PTEST_NAME@.res.1.log.txt @frama-c@ -load %{dep:@PTEST_RESULT@/@PTEST_NAME@.sav} -then-on aorai -eva > @PTEST_RESULT@/@PTEST_NAME@.res.1.log.txt
*/
/* run.config_prove
DONTRUN:
*/
void f () { }

int main () {
f();
Frama_C_show_aorai_state();
return 0;
}
