/*@
  ensures \false ;
  assigns \nothing;
*/
void job(void)
{
  int i=0, K=0;
  /*@
    loop invariant \forall integer j; 0 < j < 0 ==> \false ;
    loop assigns i ;
  */
  while (i < 10) {
    K ++;
    i ++;
  }
}
void issue(int a) {
  //@ check ko:  \exists integer j; 0 < j < 0;
  //@ check ko: (\forall integer j; 0 < j < 0 ==> \false) ==> (a == 0);
  ;
}
