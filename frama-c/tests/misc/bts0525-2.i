/* run.config
   OPT: -typecheck %{dep:@PTEST_DIR@/bts0525.i}
*/

typedef enum {E1=2, E2} T_EN1 ;

int f2(T_EN1 p2)
{
  return 0;
}
