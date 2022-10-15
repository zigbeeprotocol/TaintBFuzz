/* run.config_qualif
   DONTRUN:
*/

/*@ axiomatic Ax {
      predicate P(integer i);
      predicate Q(integer i);
      predicate R(integer i);
      predicate S(integer i);
      predicate W(integer i);
  }
*/

int x ;

void function(void){
  int i = 0;
  /*@ loop invariant       Inv_P  : P(i) ;
    @ check loop invariant Check_Q: Q(i);
    @ admit loop invariant Admit_R: R(i);
    @ loop invariant       Inv_S  : S(i);
    @ loop assigns i ; */
  while(i < 10) i++ ;

  //@ check W(i);
}
