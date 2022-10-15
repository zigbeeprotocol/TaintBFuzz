/* run.config
   OPT:-wp-gen -wp-prover why3
*/
/* run.config_qualif
   DONTRUN:
*/

/*@
  logic integer F(integer m) = (m <= 0) ? 0 : F(m) ;
  logic integer R(integer p) = (p < 0) ? -1 : R(p-1) + F(R(p-1));

  lemma R_1: \forall integer p; R(p) == R(p-1) + F(R(p-1));
  lemma R_2: \forall integer p; 0 <= R(p);
*/
