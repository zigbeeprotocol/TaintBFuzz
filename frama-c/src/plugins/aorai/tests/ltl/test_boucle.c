/* run.config*
   OPT: -aorai-ltl @PTEST_DIR@/@PTEST_NAME@.ltl -aorai-acceptance -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

/*@ requires \true;
  @ ensures 0<=\result<=1;
*/
int a() {
  return 1;
}

/*@ requires \true;
  @ ensures 1<=\result<=2;
*/
int b() {
  call_to_an_undefined_function(); 
  return 2;
}

/*@ requires \true;
  @ ensures 0<=\result<=1;
*/
int main(){
  int x=a();
  /*@ loop invariant i : 
    @      0<=x<=11;
   */
  while (x<10) {
    x+=b();
  }
  return a();
}
