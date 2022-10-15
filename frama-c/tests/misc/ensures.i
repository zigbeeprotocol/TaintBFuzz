/* run.config
PLUGIN: @EVA_PLUGINS@
 MODULE: @PTEST_NAME@
   OPT:
*/


//@ ensures *p==1;
void main(int * p) {
  *p = 0;
}
