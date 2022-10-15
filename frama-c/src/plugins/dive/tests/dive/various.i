/* run.config
STDOPT: +"-dive-from-variables main::z,f::x2 -dive-from-alarms f,main -dive-depth-limit 5"
*/

float g;

float f(float x2)
{
  float y;
  for (int i = 0 ; i < 10 ; i++)
  {
    y = x2 + 1.0;
    x2 = y * 2.0;
  }

  return x2;
}

void main()
{
  float (*pf)(float) = &f;

  float x = 3.0 + g;
  float y = f(x);
  x = x + 0.5f;
  float w = (*pf)(x);
  float z = y + w + 1.0;
}

