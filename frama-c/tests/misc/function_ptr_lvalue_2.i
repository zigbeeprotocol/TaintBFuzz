/* run.config*
PLUGIN: @EVA_PLUGINS@
 EXIT: 1
   STDOPT:
*/
void f(void) {}

int main()
  {
  void (*p)(void) = &f ;
  p = &f ;
  *p = f ;
  return 0 ;
  }
