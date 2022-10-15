/* run.config*
 EXIT: 1
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/
void f(int x) {}
void g(void) {}
void h(void) {}

void main(void)
{
  int x = 0;
  while (x < 100)
  {
    if (x % 2)
      f(x);
    else
      g();
    h();
    x++;
  }
}

