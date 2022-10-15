/* run.config
   OPT: -wp-variant-with-terminates
*/
/* run.config_qualif
   OPT: -wp-variant-with-terminates
*/

int a ;

/*@
  axiomatic Ax {
    predicate P reads a ;
    predicate Q reads \nothing ;
  }
*/

/*@ terminates P;
    assigns \nothing;
*/
void terminates_P(void);

//@ terminates Q ;
void base_call(void){
  terminates_P();
}

//@ terminates P ;
void call_same(void){
  terminates_P();
}

//@ terminates P ;
void call_change(void){
  a = 0 ;
  terminates_P();
}

/*@ terminates *p ;
    assigns \nothing ;
*/
void call_param(int* p);

//@ terminates *p ;
void call_param_same(int *p){
  call_param(p);
}

//@ terminates *p ;
void call_param_change(int *p){
  *p = 0 ;
  call_param(p);
}

//@ terminates Q ;
void variant(void){
  /*@ loop assigns i ;
      loop variant i ;
  */
  for(unsigned i = 3; i > 0; --i);
}

/*@ predicate Rel (integer old, integer new) = old > new && 0 <= old; */

//@ terminates Q ;
void general_variant(unsigned x) {
  /*@ loop assigns x ;
      loop variant x for Rel; */
  while (x > 0) x --;
}

//@ terminates Q ;
void no_variant(void){
  //@ loop assigns i ;
  for(unsigned i = 3; i > 0; --i);
}

/*@ terminates Q ;
    decreases n ; */
void decreases(unsigned n){
  if(n != 0) decreases(n-1) ;
}

/*@ terminates Q ;
    decreases n for Rel; */
void general_decreases(unsigned n){
  if(n != 0) general_decreases(n-1) ;
}

/*@ terminates Q ; */
void no_decreases(unsigned n){
  if(n != 0) no_decreases(n-1) ;
}
