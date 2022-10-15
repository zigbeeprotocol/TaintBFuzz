/* run.config*
PLUGIN: @EVA_PLUGINS@
 EXIT: 1
   STDOPT:
*/

void f(void) { }

int main(void)
  {
  void (*p)(void) = &f ;
  int x = __alignof__(p) ;
  return __alignof__(*p) ;
  }
