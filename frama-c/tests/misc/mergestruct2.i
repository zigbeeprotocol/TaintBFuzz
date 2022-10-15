/* run.config
   OPT: -print %{dep:@PTEST_DIR@/mergestruct3.i} %{dep:@PTEST_DIR@/mergestruct1.i}
*/
struct s *p;

void g(void)
{
  p = 0;
}
