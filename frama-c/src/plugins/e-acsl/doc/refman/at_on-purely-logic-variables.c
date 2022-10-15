main(void) {
  int m = 2;
  int n = 7;;
 L1: ;
  n = 4;
 L2:
  /*@ assert
      \let k = m + 1;
      \exists integer u; 9 <= u < 21 &&
      \forall integer v; -5 < v <= (u < 15 ? u + 6 : k) ==>
        \at(n + u + v > 0, K); */ ;
  /*@ assert
      \let k = m + 1;
      \exists integer u; n <= u < 21 && // [u] depends on [n]
      \forall integer v; -5 < v <= (u < 15 ? u + 6 : k) ==>
        \at(n + u + v > 0, L1); */ ;
  return 0;
}
