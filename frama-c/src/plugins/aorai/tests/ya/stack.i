/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/


int g = 0;

void push(void)
{
  g++;
}

void pop(void)
{
  //@ assert g > 0;
  g--;
}

void main(void)
{
  push();
  pop();
  push();
  push();
  pop();
  push();
  push();
  pop();
  pop();
  pop();
}
