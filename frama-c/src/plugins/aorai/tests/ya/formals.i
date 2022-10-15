/* run.config*
OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

int f(int x) { return x; }

int g(int y) { return y; }

int main() { f(1); g(2); }
