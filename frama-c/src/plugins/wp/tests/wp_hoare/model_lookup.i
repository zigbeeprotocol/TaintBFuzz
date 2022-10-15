/* run.config
   OPT: -wp-prop C
*/
/* run.config_qualif
   DONTRUN:
*/

void foo(int y){
  int x ;
  // This assertion SHALL BE VISIBLE in the VC generated for C
  //@ assert 0 <= y <= 4 ==> \false ;
  x = 1 ;
  //@ check C: x == y ;
}
