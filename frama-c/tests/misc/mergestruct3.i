/* run.config
   OPT: -print %{dep:@PTEST_DIR@/mergestruct1.i} %{dep:@PTEST_DIR@/mergestruct2.i}
   OPT: -print %{dep:@PTEST_DIR@/mergestruct2.i} %{dep:@PTEST_DIR@/mergestruct1.i}
*/
struct s { float a; } s2;

void f(void)
{
  s2.a = 1.0;
}
