/* run.config
   OPT: -wp-smoke-tests -print
 */

/* run.config_qualif
   OPT: -wp-smoke-tests
*/

void foo(void)
{
  int n = 3 ;
  /*@
    loop pragma UNROLL "completely", 4 ;
  */
  while (n>0) n--;
}
