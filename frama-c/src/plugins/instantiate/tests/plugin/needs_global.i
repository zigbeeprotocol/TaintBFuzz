/* run.config
  SCRIPT: @PTEST_NAME@
   OPT: -instantiate -check -print
*/
int i ; // needed for already_one specifciation
void already_one(void* parameter) ;

void needs_new(void* parameter) ;

void foo(void){
  int *i ;
  already_one(i);
  needs_new(i);
}
