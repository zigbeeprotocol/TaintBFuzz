/* run.config
   OPT: -wp-definitions-terminate -wp-declarations-terminate
*/
/* run.config_qualif
   OPT: -wp-definitions-terminate -wp-declarations-terminate
*/

//@ assigns \nothing ;
void gt(int);
//@ assigns \nothing ;
void ht(int);

/*@ terminates \false ;
    assigns \nothing ; */
void gnt(int i);

/*@ terminates i == 0 ;
    assigns \nothing ; */
void hnt(int i);

//@ requires f == gt || f == ht ;
void t_spec(void (*f) (int)){
  //@ calls gt, ht ;
  f(0);
}

/*@ behavior B1:
      assumes x == 0 ;
      requires f == hnt ;
    behavior B2:
      assumes x != 0 ;
      requires f == gt ;
    complete behaviors ;
    disjoint behaviors ;
*/
void t_spec_in_bhv(void (*f) (int), int x){
  //@ calls gt, hnt ;
  f(x);
}

//@ requires f == gnt || f == hnt ;
void no_t_spec(void (*f) (int)){
  //@ calls gnt, hnt ;
  f(0);
}

/*@ behavior B1:
      assumes x == 0 ;
      requires f == gnt ;
    behavior B2:
      assumes x != 0 ;
      requires f == hnt ;
    complete behaviors ;
    disjoint behaviors ;
*/
void no_t_spec_in_bhv(void (*f) (int), int x){
  //@ calls gnt, hnt ;
  f(0);
}

//@ requires f == gt || f == hnt ;
void no_t_spec_cond(void (*f) (int)){
  //@ calls gt, hnt ;
  f(1);
}

/*@ requires f == gt || f == ht ;
    requires g == hnt ;
*/
void no_t_spec_cond_m(void (*f) (int), void (*g) (int)){
  //@ calls gt, ht ;
  f(0);

  //@ calls hnt ;
  g(1);
}

void warns_recursive(void (*f) (int)){
  f(42);
}
