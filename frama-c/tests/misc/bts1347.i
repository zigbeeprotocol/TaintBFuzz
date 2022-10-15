/* run.config
 PLUGIN: @EVA_PLUGINS@ report
 MODULE: @PTEST_NAME@
   OPT:  @EVA_OPTIONS@ -then -report
*/

int f(int *x) {
  return *x;
}

int g(int *x) {
  return *(x++);
}
