/* run.config
   CMD: @frama-c@ -wp-share @PTEST_SHARE_DIR@ -wp-msg-key cluster,shell,print-generated -wp-prover why3 -wp-warn-key "pedantic-assigns=inactive"
   OPT: -wp-model Typed -wp -wp-gen -wp-print -then -wp-model Typed+ref -wp -wp-gen -wp-print
*/

/* run.config_qualif
   OPT: -wp-msg-key print-generated -wp-model Typed -then -wp -wp-model Typed+ref
*/

//@ predicate P(integer a);

//@ ensures P(\result);
int f(int *p,int k) { return p[k]; }
