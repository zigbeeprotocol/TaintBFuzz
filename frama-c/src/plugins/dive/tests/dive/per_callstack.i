/* run.config
STDOPT: +"-dive-from-variables main::w -dive-depth-limit 20"
*/

float f(float x) {
  float y = x + 1;
  return y;
}

float main(float a, float b, float c)
{
  float x = f(a);
  float y = f(b);
  float z = f(c);
  float w = x + y + z;
  return w;
}

