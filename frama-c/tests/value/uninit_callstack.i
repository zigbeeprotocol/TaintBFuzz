/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -eva @EVA_CONFIG@ -eva-no-show-progress -eva-print-callstacks -eva-no-results
*/
int *p, x;
void f(void)
{
  if (*p) x = 1;
}

int main(){
  int a;
  p = &a;
  f();
}
