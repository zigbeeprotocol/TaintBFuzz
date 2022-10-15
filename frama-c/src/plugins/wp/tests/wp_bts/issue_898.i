struct S {
  int valid;
  double value;
};

/*@
  requires \is_finite(val);
  ensures \eq_double(\result.value,val);
  assigns \nothing;
*/
struct S job(double val) {
  struct S result = { 0, val };
  return result;
}
