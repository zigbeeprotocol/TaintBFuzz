/* run.config
OPT: -journal-disable -wp-model Hoare -wp-verbose 2
OPT: -journal-disable -wp-model Typed -wp-verbose 2 -wp-prop @assigns
*/

/* run.config_qualif
OPT: -journal-disable -rte -wp -wp-model Hoare -wp-par 1 -wp-msg-key shell
*/
/*----------------------------------------------------------------------------*/

/* This file is to test the strategy generation, so it doesn't need to be tested
 * for different models. Let's choose examples that work with Hoare,
 * except to test assign properties that need pointer aware memory model (ex Typed).
 */

/*----------------------------------------------------------------------------*/
/* we shouldn't be able to prove ko1 from ko2 and then ko2 from ko1 */
/*@ ensures qed_ko: ko1 : \result == x+1;
    ensures qed_ko: ko2 : \result == x+1;
*/
int bts0513 (int x) {
  return x;
}

int bts0513_bis (int x) {
  int i;
  //@ assert qed_ko: ko1 : x > 0;
  //@ assert qed_ok: ok : x > 0;
  return x;
}
