/* run.config
STDOPT: +"-dive-from-variables g::x -dive-depth-limit 7"
*/

float g(float x) {
  float y = x + 1;
  return y;
}

float f1(float x) { return g(x); }
float f2(float x) { return g(x); }
float f3(float x) { return g(x); }

float main(float x)
{
  float z = f1(x) + f2(x) + f3(x);
  return z;
}

