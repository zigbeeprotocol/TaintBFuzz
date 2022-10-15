/* run.config
 PLUGIN: @EVA_PLUGINS@
 MODULE: @PTEST_NAME@
   OPT: -eva @EVA_CONFIG@ -eva-slevel-function main:10
*/

void main() {

  int i, j = 0;

  for (i=0; i<10; i++) {
    j++;
  }

  //@ assert i == j;

}
