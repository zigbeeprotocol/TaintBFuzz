/* run.config
 COMMENT: depends from files mentionned into "abs.driver"
 DEPS: abs.why
   OPT: -wp-driver %{dep:@PTEST_DIR@/abs.driver}
 */
/* run.config_qualif
 COMMENT: depends from files mentionned into "abs.driver"
 DEPS: abs.why
   OPT: -wp -wp-driver %{dep:@PTEST_DIR@/abs.driver} -wp-prover alt-ergo
*/
/*@ axiomatic Absolute { logic integer ABS(integer x) ; } */

/*@ ensures \result == ABS(x) ; */
int abs(int x)
{
  if (x < 0) return -x ;
  return x ;
}
