/* run.config
 SCRIPT: @PTEST_NAME@
   OPT: -instantiate -check -print
*/
void mine(void* parameter) ;

void foo(void){
  int *i ;
  float *f ;

  mine(i);
  mine(f);
}
