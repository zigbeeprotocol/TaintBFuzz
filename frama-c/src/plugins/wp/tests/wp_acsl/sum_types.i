/* run.config
   OPT:-wp-prover=why3 -wp-gen -wp-msg-key print-generated
*/
/* run.config_qualif
   DONTRUN:
*/

/*@
  axiomatic A {
    type InAxiomatic = IAu(unsigned)
                     | IAc(char)
                     | IAi(integer) ;

    predicate P(InAxiomatic a) reads \nothing ;
  }
  lemma LA: \forall InAxiomatic a ; P(a) ;
*/
/*@
  type AtTopLevel = TLu(unsigned)
                  | TLc(char)
                  | TLi(integer) ;

  axiomatic X {
    predicate Q(AtTopLevel a) reads \nothing ;
  }
  lemma LB: \forall AtTopLevel a ; Q(a) ;
*/
/*@
  type Rec = Nil | C(int, Rec) ;

  axiomatic Y {
    predicate R(Rec a) reads \nothing ;
  }
  lemma LC: \forall Rec a ; R(a) ;
*/
