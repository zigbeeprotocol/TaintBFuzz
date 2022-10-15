/* run.config_qualif
  SCRIPT: @PTEST_NAME@
   OPT: -wp-msg-key shell
*/
int empty (int c){
  c = c < 0 ? c + 10 : c+100;
  int tmp;
  tmp = c;
  /*@ assert \true;*/
  return tmp;
}
