union { int i ; float f ; } bits;

float r;

int main () {
  bits.i = unknown_fun();
  r = 1.0 + bits.f;
  return r > 0.;
}
  
