/* run.config
STDOPT: +"-dive-from-variables main::r -dive-depth-limit 10"
*/

int g;

float f(float x) {
  g = g + x;
  return g;
}

void main(float a)
{
  int x1 = 3;
  int x2 = 39;
  int r = f(x1) + f(x2);
}
