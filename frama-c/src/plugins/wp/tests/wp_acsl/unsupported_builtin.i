/* run.config
  SCRIPT: @PTEST_NAME@
  OPT:
*/
/* run.config_qualif
  DONTRUN:
*/
/*@ ensures unimplemented_builtin ; */
void foo(void);

int main(void){
  foo();
  //@ assert \true ;
}
