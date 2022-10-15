/* run.config
   DONTRUN:
 */

/* run.config_qualif

   OPT: -wp-prover script,alt-ergo @USING_WP_SESSION@
 */

typedef unsigned short ushort;

/*@
  lemma res_n: \forall ushort off; ! (off & 0x8000) ==> off < 0x8000;
  lemma res_y: \forall ushort off; (off & 0x8000) ==> off >= 0x8000;
*/
