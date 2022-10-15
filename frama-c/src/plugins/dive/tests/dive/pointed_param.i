/* run.config
STDOPT: +"-dive-from-variables main::y -dive-depth-limit 6"
*/

float h(float *p)
{
  return *p - 1;
}

float g(float *p)
{
  return h(p);
}

float f(float x)
{
  return g(&x);
}

float main(float x)
{
  float y = f(x) + 1;
  return y;
}

