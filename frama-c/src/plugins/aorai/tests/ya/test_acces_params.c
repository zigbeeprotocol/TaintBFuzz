/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

int status=0;
int rr=1;
//@ global invariant inv : 0<=rr<=5000;

/*@ requires rr<5000;
  @ behavior j :
  @  ensures rr<5001;
*/
void opa(int i, int j) {
  rr=i+j;
}


int opb () {
  status=1;
  return status*3;
}

int main(){

  if (rr<5000) opa(rr,300);
  rr=opb();

  return 1;
}
