/* run.config
STDOPT: +"-dive-from-variables main::z"
*/

float g;

float main(float x)
{
  float y = x + 1;
  g = y;
  float z = g + x;
  return z;
}

