/*@
  requires x >= 0;
  ensures \result * \result <= x < (\result + 1) * (\result + 1);
 */
int sqrt (int x) {
  if (x<=0) return 0;
  int res = 1;
  int prod = 1;
  while (prod < x) {
    prod = prod + 2*res + 1;
    res++;
  }
  return res;
}

/*
Local Variables:
compile-command: "frama-c -jessie-analysis -jessie-int-model exact -jessie-gui sqrt.c"
End:
*/
