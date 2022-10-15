/* run.config_qualif
   OPT: -wp-prover=Alt-Ergo:1.2.0
 */

/*@ ensures \result == a * b ; */
int job(int a,int b) { return (a - 1)*b + b ; }
