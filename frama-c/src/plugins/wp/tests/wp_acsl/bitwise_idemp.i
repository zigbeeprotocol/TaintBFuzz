/*
 X Y | X & Y | X & (X & Y)
     |       |
 0 0 |   0   |     0
 0 1 |   0   |     0
 1 0 |   0   |     0
 1 1 |   1   |     1
*/

void land(int x, int a, int b, int c, int d) {
  //@ check A:  (x ? c == a : c == b)  ==> (a & (b & c)) == (a & b) ;
  //@ check B:  (x ? c == a : c == b)  ==> ((a & b) & c) == (a & b) ;
}

/*
 X Y | X | Y | X | (X | Y)
     |       |
 0 0 |   0   |     0
 0 1 |   1   |     1
 1 0 |   1   |     1
 1 1 |   1   |     1

*/

void lor(int x, int a, int b, int c, int d) {
  //@ check A:  (x ? c == a : c == b)  ==> (a | (b | c)) == (a | b) ;
  //@ check B:  (x ? c == a : c == b)  ==> ((a | b) | c) == (a | b) ;
}

/*
 X Y | X ^ Y | X ^ (X ^ Y)
     |       |
 0 0 |   0   |     0
 0 1 |   1   |     1
 1 0 |   1   |     0
 1 1 |   0   |     1
*/

void lxor(int x, int a, int b, int c, int d, int e) {
  //@ check A:  (x ? c == a && e == b : c == b && e == a)  ==> (a ^ (b ^ c)) == e ;
  //@ check B:  (x ? c == a && e == b : c == b && e == a)  ==> ((a ^ b) ^ c) == e ;
}
