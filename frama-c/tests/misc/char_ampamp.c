/* run.config
 PLUGIN: @EVA_PLUGINS@
STDOPT:
*/

char c=1;
int y;

void g(int y, int x)
{
  Frama_C_show_each_x(x);
}

int main()
{
  y = 42 && c;
  g(c, 42 && c);
  return 0;
}
