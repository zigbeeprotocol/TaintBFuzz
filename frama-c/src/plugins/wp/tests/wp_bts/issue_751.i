//@ requires 0 < Nb <= 8 ;
void acquire(int R,int Nb,int * Data)
{
  if ( (R & 0x0F00) >> 8 == Nb ) {
    int j = 0 ;
    /*@
      loop invariant RANGE: 0 <= j <= Nb ;
      loop assigns j, Data[0..7] ;
    */
    while (j < Nb) {
      Data[j] = 0 ;
      j++;
    }
  }
}

/*@ requires pos_max:        k>0 && (0 <= a || 0 <= b) ==> ( a/k <= b <==> a < b*k + k ) ;
  @ requires neg_max:        k>0 && (a <= 0 || b <  0) ==> ( a/k <= b <==> a <= b*k )    ;
  @ requires pos_min:        k>0 && (0 <= a || 0 <  b) ==> ( b <= a/k <==> b*k <= a )    ;
  @ requires neg_min:        k>0 && (a <= 0 || b <= 0) ==> ( b <= a/k <==> b*k - k < a ) ;
  @ requires strict_pos_max: k>0 && (0 <= a || 0 <  b) ==> ( a/k < b  <==> a < b*k )     ;
  @ requires strict_neg_max: k>0 && (a <= 0 || b <= 0) ==> ( a/k < b  <==> a <= b*k - k );
  @ requires strict_pos_min: k>0 && (0 <= a || 0 <= b) ==> ( b < a/k  <==> b*k + k <= a );
  @ requires strict_neg_min: k>0 && (a <= 0 || b <  0) ==> ( b < a/k  <==> b*k < a )     ;
  @ assigns \nothing;
*/
int checks (int a, int b, int k) ;

int issue_751(int V)
{ int n = 2;
  int k = 1<<n;
  //@ check (V >> n) <=  16 <==>  V <   16*k + k;
  //@ check (V >> n) <= -16 <==>  V <= -16*k;
  //@ check  16 <= (V >> n) <==>  16*k     <= V;
  //@ check -16 <= (V >> n) <==> -16*k - k <  V;

  checks ( 21, V, 3);
  checks (-27, V, 7);

  checks (V,  5, 19);
  checks (V, -7, 23);
 
  return V;
}
