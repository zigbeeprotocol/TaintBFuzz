/* run.config
STDOPT: +"-dive-from-variables main::res -dive-depth-limit 5"
*/

int f(int x, int y)
{
  const c = x + 1;
  int w = y + 1;
  return c + w;
}

int main(int i)
{
  int res = f(i, 2*i);
  return res;
}
