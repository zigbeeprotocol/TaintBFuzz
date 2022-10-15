/*@ assigns \result \from x; */
int mod3 (int x) {
  Frama_C_show_each(x);
  if ((x / 3) * 3 == x) return 0;
  else return 1 + mod3(x-1);
}

void main (int x) {
  int r = mod3(x);
}
