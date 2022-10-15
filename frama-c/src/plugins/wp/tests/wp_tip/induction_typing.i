/* run.config

   OPT: -wp-par 1 -wp-prop X -wp-no-print -wp-prover qed,script -wp-msg-key script @USING_WP_SESSION@
*/
/* run.config_qualif
   DONTRUN:
*/

/* This test is meant to check that we do not generate a ill-formed VC with the
   induction tactic. Here, the bug happened when triggering an induction on i
   (i was replaced with true) when proving that X is preserved . The example is
   complex because we need to have some State variable for i. */

extern int LIST;
extern unsigned int cpt;
extern unsigned int A[];

/*@
	axiomatic call {
    logic \list<integer> list{L2} reads LIST;
  }
*/

/*@
	ensures cpt == \old(cpt) + 1;
	ensures A[\old(cpt)] == \old(i);
	ensures list == (\old(list) ^ [| 1 |]);
	assigns cpt, LIST;
*/
void f(unsigned int i);


/*@
  requires list == [| |];
	requires cpt == 0;
*/
void function(unsigned int Max)
{
	unsigned int i = 0;
	/*@
    loop invariant 0 <= cpt == i <= 42;
		loop invariant X: list == (\at(list,LoopEntry) ^ ([| 1 |]  *^ i));
		loop assigns i, cpt, LIST;
	*/
	while (i < Max) {
		f(i);
		i ++;
	}

  return;
}
