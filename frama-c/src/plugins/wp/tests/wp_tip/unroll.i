/* run.config
   DONTRUN:
*/

/* run.config_qualif

   OPT: -wp-prover script,none @USING_WP_SESSION@
 */

/*@
  lemma SUM:
    \forall \list<integer> a;
    \forall integer p,q;
    0 <= p ==> 0 <= q ==>
    (a *^ (p+q)) == ((a *^ p) ^ (a *^ q)) ;
*/

/*@
  lemma RIGHT:
    \forall \list<integer> a;
    \forall integer n;
    0 < n ==>
    (a *^ n) == ((a *^ (n-1)) ^ a) ;
*/

/*@
  lemma LEFT:
    \forall \list<integer> a;
    \forall integer n;
    0 < n ==>
    (a *^ n) == (a ^ (a *^ (n-1))) ;
*/
