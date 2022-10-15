/* run.config
STDOPT: +"-dive-from-variables g::r -dive-depth-limit 20"
*/

float f(float z) {
  return z;
}

float g(float y) {
  float z = f(y);
  float r = y + z;
  return r;
}

float h(float x) {
  float y = f(x);
  float r = g(y);
  return r;
}

float i(float x) {
  return g(x);
}


void main(float a)
{
  h(a);
  i(a);
}

