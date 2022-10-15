/* run.config
 PLUGIN: @EVA_PLUGINS@ constant_propagation
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -save @PTEST_NAME@.sav @EVA_OPTIONS@ -semantic-const-folding @PTEST_FILE@ > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav}"
 MODULE: @PTEST_NAME@
   OPT: -eva @EVA_OPTIONS@
*/
int f(int x) {
  return x + x;
}

int main() {
  int x = 2;
  int y = f(x);
  /*@ assert y == 4; */
  return x * y;
}
