/* run.config_qualif
   OPT: -wp-fct "g"
*/

/*@ axiomatic ax {
  @ predicate ExitF(integer x);
  @ predicate ExitP(integer x);
  @ predicate PostF(integer x);

} */

//@ assigns \nothing; ensures PostF(x); exits ExitF(x) ;
int f(int x);

// corrected.
//@ requires ExitF(max) ==> ExitP(max); assigns \nothing; exits ok:ExitP(max);
void g (int max) {
  int tmp = f(max);
  //@ loop assigns ok:tmp;
  while (tmp<=max) {
     tmp ++;
  }
}
