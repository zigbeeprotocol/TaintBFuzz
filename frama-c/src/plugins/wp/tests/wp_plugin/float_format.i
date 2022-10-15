/* run.config_qualif
   OPT: -wp-prover alt-ergo -wp-steps 5 -wp-timeout 100
*/

//@ ensures KO: \result == 0.2 + x ;
float output(float x)
{
  return 0.2 + x ;
}
