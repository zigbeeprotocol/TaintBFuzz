/* run.config*
 PLUGIN: @EVA_PLUGINS@
 MODULE: @PTEST_NAME@
   OPT:
*/

int main(int c) {

  int x = 0;
  int y = 0;

  int *p = &x;
  int *q = &y;

  if (c) q = &x;
  if (p<=q) x++;

  return *q;
}
