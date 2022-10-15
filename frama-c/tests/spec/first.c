/* run.config
   OPT: -print %{dep:@PTEST_DIR@/third.c} %{dep:@PTEST_DIR@/second.c}
*/
/*@ behavior b:
  requires \valid(first);
  ensures \result == 0;*/
int bar(int *first);

void main (int * c) {
  bar(c);
}
