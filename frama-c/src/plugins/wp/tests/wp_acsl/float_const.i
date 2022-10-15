/* run.config
   OPT:-wp-gen -wp-prover=why3 -wp-msg-key=print-generated -kernel-warn-key parser:decimal-float=active
*/
/* run.config_qualif
   OPT:
*/

void float_convertible(float f){
  double d = f ;
  if(f == 0.1f){
    //@ check f != 0.1 ;
    //@ check f == (float)0.1 ;
    //@ check f != (double)0.1 ;
    //@ check (float) d == f ;
  }
}
void double_convertible(double d){
  double x = (float) d ;
  if(d == 0.1){
    //@ check d != 0.1 ;
    //@ check d == (double)0.1 ;
    //@ check d != (float)0.1 ;
    //@ check x == (float) d ;
  }
}
