/* run.config

   OPT: -wp-par 1 -wp-no-print -wp-prover qed,script -wp-msg-key script @USING_WP_SESSION@

   OPT: -wp-par 1 -wp-no-print -wp-prover qed,script -wp-msg-key script @USING_WP_SESSION@
*/
/* run.config_qualif
   DONTRUN:
*/

/*@
  check lemma and_modulo_us_255:
    \forall unsigned short us ; (us & 0xFF) == us % 0x100 ;
*/

/*@
  check lemma and_modulo_u:
    \forall unsigned us, integer shift;
      0 <= shift < (sizeof(us) *  8) ==> (us & ((1 << shift) - 1)) == us % (1 << shift);
*/
