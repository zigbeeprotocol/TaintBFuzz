/* run.config
   DONTRUN:
*/

/* run.config_qualif

   OPT: -wp-prover script,alt-ergo -wp-timeout 1 @USING_WP_SESSION@
*/

typedef unsigned int uint;
typedef unsigned short ushort;

/*@
  lemma j_incr_char:
    \forall uint ui, char c;
    0 <= ui <= 1000 && 0 <= ui + c <= 1000 ==>
      ui + c == (uint)(ui + (uint)(c)) ;
*/

/*@
  lemma j_incr_short:
    \forall uint ui, short s;
    0 <= ui <= 1000 && 0 <= ui + s <= 1000 ==>
      ui + s == (uint)(ui + (uint)(s)) ;
*/
