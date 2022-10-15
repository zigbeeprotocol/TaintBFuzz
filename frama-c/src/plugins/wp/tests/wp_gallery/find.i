/* run.config
   OPT: -wp-no-print -wp-rte
*/

/* run.config_qualif
   OPT: -then -wp-rte -wp
*/

/*@ predicate IsValueOk(integer u, integer v) = u == v;
*/

/*@ predicate InRange(integer start, integer k,  integer last) = 
      start <= k <= last;
*/
/*@ predicate Found(int * p, integer n, integer v) =
      \exists integer k;
        InRange(0,k,n-1) && IsValueOk(p[k],v);
*/

/*@ requires Natural:    0 <= n;
  @ requires Valid:      \valid(p + (0 .. n-1));
  @ ensures  Range:      InRange(0,\result,n);
  @ ensures  NoneBefore: !Found(p,\result,v);
  @ behavior not_found:
      assumes ! Found(p,n,v);
      ensures \result == n ;
  @ behavior found:
      assumes Found(p,n,v);
      ensures \result < n ;
      ensures IsValueOk(p[\result],v) ;
  @ disjoint behaviors found, not_found;
  @ complete behaviors found, not_found;
 */
int find(int * p, int n, int v) {
  int i = 0;
  /*@ loop assigns i;
    @ loop invariant Valid:    \valid(p + (0 .. i-1));
    @ loop invariant Range:    InRange(0,i,n);
    @ loop invariant NotFound: !Found(p,i,v);
    @ loop variant   Decrease: n - i;
  */
  for (; i < n ; i++)
    if (p[i] == v)
      break;
  return i;
}
//----------------------------------------------------------
/*@ predicate IsValueOk_ptr(int * p, integer v) = *p == v;
*/

/*@ predicate InRange_ptr(int * start, int * p,  int * last) =
         \base_addr(start) == \base_addr(last)
      && \base_addr(start) == \base_addr(p)
      && start <= p <= last ;
*/

/*@ predicate Found_ptr(int * start, int * last, integer v) =
       \exists int* pk;
         InRange_ptr(start, pk, last-1) && IsValueOk_ptr(pk,v);
*/

/*@ requires Ordered:    p <= q && \base_addr(p) == \base_addr(q);
  @ requires Valid:      \valid(p + (0 .. (q-p)-1));
  @ ensures  Range:      InRange_ptr(p,\result,q) ;
  @ ensures  NoneBefore: !Found_ptr(p,\result,v);
  @ behavior not_found:
      assumes !Found_ptr(p,q,v);
      ensures \result == q;
  @ behavior found:
      assumes Found_ptr(p,q,v);
      ensures \result < q ;
      ensures IsValueOk_ptr(\result,v) ;
  @ disjoint behaviors found, not_found;
  @ complete behaviors found, not_found;
 */
int * find_ptr(int * p, int * q, int v) {
  /*@ loop assigns p;
    @ loop invariant Valid:    \valid(\at(p,LoopEntry) + (0 .. (\at(p,LoopEntry)-p-1)));
    @ loop invariant Range:    InRange_ptr(\at(p,LoopEntry),p,q);
    @ loop invariant NotFound: !Found_ptr(\at(p,LoopEntry),p,v);
    @ loop variant   Decrease: q - p;
  */
  for (; p < q; p++) {
    if (*p == v)
      //@ assert Hack: IsValueOk_ptr(p,v);
      break;
   }
  return p;
}
//----------------------------------------------------------
/*@ requires Ordered: p <= q && \base_addr(p) == \base_addr(q);
  @ requires Valid:   \valid(p + (0 .. (q-p)-1));
  @ ensures  Last:    \result == q ;
*/
int * iter_ptr(int * p, int * q) {
  /*@ loop assigns p;
    @ loop invariant Valid:    \valid(\at(p,LoopEntry) + (0 .. (\at(p,LoopEntry)-p-1)));
    @ loop invariant Range:    InRange_ptr(\at(p,LoopEntry),p,q);
    @ loop variant   Decrease: q - p;
  */
  for (; p < q ; p++);
  return p;
}
