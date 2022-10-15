int main(void) 
{
  int a, b ,c;
  a = 5;
  /*@ behavior pre_f:
        ensures b == -\old(a);
      
      behavior pre_f_pos:
        assumes a >= 0;
        ensures b <= 0;
        assigns b, c;
      
      behavior pre_f_neg:
        assumes a < 0;
        ensures b > 0;
        assigns b;
  */
  b = f(a,& c);
  /*@ assert rte: signed_overflow: -2147483648 <= b+c; */
  /*@ assert rte: signed_overflow: b+c <= 2147483647; */
  return (b + c);
}


