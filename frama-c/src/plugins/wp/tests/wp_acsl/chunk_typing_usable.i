/* run.config
   OPT: -wp-gen -wp-rte -wp-prover why3 -wp-msg-key print-generated
*/
/* run.config_qualif
   OPT: -wp-rte -wp-prover alt-ergo
*/

/*@
  axiomatic Occ{
    logic integer occ{L}(int value, int* p, integer f, integer t)
      reads p[f .. t-1];

    axiom empty{L}:
      \forall int v, int* p, integer f, t;
        f >= t ==> occ{L}(v, p, f, t) == 0;

    axiom is{L}:
      \forall int v, int* p, integer f, t;
        (f < t && p[t-1] == v) ==> occ(v,p,f,t) == 1+occ(v,p,f,t-1);

    axiom isnt{L}:
      \forall int v, int* p, integer f, t;
        (f < t && p[t-1] != v) ==> occ(v,p,f,t) == occ(v,p,f,t-1);
  }
*/

/*@
  requires b < e <= 1000 ;
  ensures \forall int v ; v != a[e-1] ==> occ(v,a,b,e) == occ(v,a,b,e-1);
*/
void usable_axiom(int* a, unsigned b, unsigned e){

}

/*@
  lemma provable_lemma:
    \forall int v, int* p, integer f, s, t;
    f <= s <= t ==> occ(v,p,f,t) == occ(v,p,f,s) + occ(v,p,s,t) ;
*/

/*@
  requires b < s <= e;
  ensures \forall int v ; occ(v,a,b,e) == occ(v,a,b,s) + occ(v,a,s,e) ;
*/
void usable_lemma(int* a, unsigned b, unsigned s, unsigned e){

}
