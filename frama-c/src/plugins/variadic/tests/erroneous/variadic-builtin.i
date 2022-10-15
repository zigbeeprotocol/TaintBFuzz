/* run.config*
 EXIT: 3
   STDOPT:
*/
extern void Frama_C_show_each_warning(char const * , ...);

void main(void)
{
  Frama_C_show_each_warning("Test warning");
  void (*p)(char const * , ...) = &Frama_C_show_each_warning;
  p("This won't work as expected");
}

