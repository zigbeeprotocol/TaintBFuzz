/* run.config

   OPT: -wp-par 1 -wp-no-print -wp-prover qed,script -wp-msg-key script @USING_WP_SESSION@
*/
/* run.config_qualif
   DONTRUN:
*/

/*@ axiomatic X {
      predicate P ;
      predicate Q ;
      predicate R ;
      predicate S ;

      predicate Pi (integer x);
      predicate Qi (integer x);

      logic boolean LP ;
      logic boolean LQ ;
    }
*/

int a, b;

/*@ assigns \nothing;
  @ ensures P ; */
void gen_P(void);

/*@ assigns \nothing;
  @ ensures Q ; */
void gen_Q(void);

/*@ assigns \nothing;
  @ ensures R ; */
void gen_R(void);

//@ ensures S ;
void test_step_branch(void) {
  if (a < b) {
    gen_P();
  } else {
    gen_Q();
  }
}

/*@ requires P || Q || R ;
  @ ensures S ; */
void test_step_or(void) {}

/*@ requires P && Q && R ;
  @ ensures S ; */
void test_step_and(void) {}

/*@ requires LP == LQ ;
  @ ensures S ; */
void test_step_peq(void) {}

/*@ requires LP != LQ ;
  @ ensures S ; */
void test_step_pneq(void) {}

/*@ requires a != b ;
  @ ensures S ; */
void test_step_neq(void) {}

/*@ requires a <= b ;
  @ ensures S ; */
void test_step_leq(void) {}

/*@ requires a < b ;
  @ ensures S ; */
void test_step_lt(void) {}

/*@ requires (a < b) ? P : Q ;
  @ ensures S ; */
void test_step_if(void) {}

/*@ requires \forall integer i ; (a < b) ? P && Pi(i) : Q && Qi(i) ;
  @ ensures S ; */
void test_step_fa_if(void) {}

/*@ requires \forall integer i ; Pi(i) || P || Qi(i) || Q || R ;
  @ ensures S ; */
void test_step_fa_or(void) {}

/*@ requires \forall integer i ; Pi(i) && P && Qi(i) && Q && R ;
  @ ensures S ; */
void test_step_fa_and(void) {}

/*@ requires P && a <= b ;
  @ ensures Q ; */
void test_inside_leq(void) {}

/*@ requires P && a < b ;
  @ ensures Q ; */
void test_inside_lt(void) {}

/*@ requires P && a != b ;
  @ ensures Q ; */
void test_inside_neq(void) {}

/*@ requires S ;
  @ ensures P && Q && R ; */
void test_goal_and(void) {}

/*@ requires S ;
  @ ensures LP == LQ ; */
void test_goal_eq(void) {}

/*@ requires S ;
  @ ensures LP != LQ ; */
void test_goal_neq(void) {}

/*@ requires S ;
  @ ensures (a < b) ? P : Q ; */
void test_goal_if(void) {}

/*@ requires S ;
  @ ensures \exists integer i ; P && Q && Pi(i) && Qi(i) ; */
void test_goal_ex_and(void) {}

/*@ requires S ;
  @ ensures \exists integer i ; P || Q || Pi(i) || Qi(i) ; */
void test_goal_ex_or(void) {}

/*@ requires S ;
  @ ensures \exists integer i ; (a < b) ? Pi(i) && Qi(i) : P && Q ; */
void test_goal_ex_if(void) {}

/*@ requires S ;
  @ ensures \exists integer i ; Pi(i) && Q ==> Qi(i); */
void test_goal_ex_imply(void) {}
