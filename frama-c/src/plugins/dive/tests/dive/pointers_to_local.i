/* run.config
STDOPT: +"-dive-from-variables main::x -dive-depth-limit 5"
*/

void g(float *p) {
  float x = *p;
  *p = x + 1.0f;
}

void f1(float *p) {
  g(p);
}

void f2(float *p) {
  float x = *p;
  *p += x + 2.0f;
}

float main()
{
  float x = 0.0f;
  f1(&x);
  f2(&x);
  return x;
}
