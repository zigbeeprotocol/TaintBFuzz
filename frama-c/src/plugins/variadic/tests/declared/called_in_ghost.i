/* run.config
 SCRIPT: @PTEST_NAME@
   OPT: -kernel-warn-key ghost:bad-use=inactive -print
*/
// Note: we deactivate "ghost:bad-use" to check that printing goes right
/*@ assigns \nothing ; */
void function(int e, ...);

void foo(void){
  //@ ghost function(1, 2, 3, 4);
}

/*@ assigns \nothing ; */
int function_wr(int e, ...);

void bar(void){
  //@ ghost int x = function_wr(1, 2);
  //@ ghost x = function_wr(1, 2);
}
