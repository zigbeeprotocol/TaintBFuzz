/* run.config_qualif
   OPT: -wp-timeout 1
 */

/*@
  axiomatic Th {

  predicate P(integer p);
  predicate Q(integer q);
  predicate R(integer r);

  axiom       A: \forall integer x; P(x) ==> Q(x);
  check lemma C: ko: \forall integer x; Q(x) ==> R(x);
  lemma       L: ko: \forall integer x; P(x) ==> R(x); // C is not used

  }
 */

/*@
  axiomatic Cfg {
  logic integer F(integer x);
  predicate A(integer x);
  predicate B(integer x);
  predicate CA1(integer x);
  predicate CA2(integer x);
  predicate CB1(integer x);
  predicate CB2(integer x);

  axiom AFB: \forall integer x; A(x) ==> B(F(x));
  axiom ACB1: \forall integer x; A(x) ==> CB1(F(x));
  axiom CA1B2: \forall integer x; CA1(x) ==> CB2(F(x));

  }
 */

/*@
  ensures \result == F(x);
  assigns \nothing;
 */
int f(int x);

/*@
  requires A:               A(x);
  check requires CA1:     CA1(x);
  check requires CA2: ko: CA2(x);
  ensures B:                B(\result);
  check ensures CB1:      CB1(\result);
  check ensures CB2: ko:  CB2(\result); // CA1 is not used
  assigns \nothing;
*/
int job(int x) {
  return f(x);
}

/*@
  requires A(x);
  requires CA1(x);
  ensures R: B(\result);
  ensures R1: ko: CB1(\result); // CB1 is not used from job
  ensures R2: ko: CA2(x);   // CA2 is not used from job
  assigns \nothing;
*/
int caller(int x)
{
  return job(x); // CA2 is not proved
}

void loop () {
  int j = 0;
  /*@ check loop invariant false_but_preserved: j == 10;
      loop assigns i;
   */
  for (int i = 0; i< 10; i++);
  /*@ check implied_by_false_invariant: j == 10; */
}
