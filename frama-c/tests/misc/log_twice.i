/* run.config
 PLUGIN: @EVA_PLUGINS@
 MODULE: @PTEST_NAME@
   OPT: @EVA_CONFIG@
*/
int* f() {
  int x;
  return &x;
}

void main(int x) {
  int *p = f();
  *p = 1;
}
