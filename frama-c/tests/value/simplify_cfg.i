/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -simplify-cfg -keep-switch -eva @EVA_CONFIG@
   OPT: -simplify-cfg -eva @EVA_CONFIG@
*/
int main(int x, int y) {
  int z = 0;
  char c = 'c';
  switch (x) {
  case 0: z=(int)c;
  default: z++;
  }
  return z;
}
