/* run.config
   OPT:-wp-rte -wp-no-let -wp-gen -wp-prover why3 -wp-msg-key print-generated
*/
/* run.config_qualif
   DONTRUN:
*/

struct X {
  char a ;
  short b ;
  int c ;
};

void foo(struct X* p){
  struct X r = *p ;
  *p = r ;
}
