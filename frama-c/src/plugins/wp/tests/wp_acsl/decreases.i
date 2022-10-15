/* run.config
   OPT:
   OPT: -wp-variant-with-terminates
*/
/* run.config_qualif
   OPT:
   OPT: -wp-variant-with-terminates
*/

/*@ predicate Rel (integer old, integer new) = old > new && 0 <= old; */

// Simple recursion

/*@ terminates \true ;
    decreases n ; */
unsigned fact(unsigned n){
  return n == 0 ? 1 : n * fact(n-1);
}

/*@ decreases n ; */
unsigned fails_fact(unsigned n){
  return n == 0 ? 1 : n * fails_fact(n);
}

/*@ decreases n for Rel ; */
unsigned facto_gen(unsigned n){
  return n == 0 ? 1 : n * facto_gen(n-1);
}

/*@ decreases n for Rel ; */
unsigned fails_facto_gen(unsigned n){
  return n == 0 ? 1 : n * fails_facto_gen(n);
}

// Simple recursion + termination

/*@ terminates n >= 0 ;
    decreases n ; */
int fact_i(int n){
  return n == 0 ? 1 : n * fact_i(n-1);
}

/*@ terminates n >= -1 ;
    decreases n for Rel ; */
int fails_fact_i(int n){
  return n == 0 ? 1 : n * fails_fact_i(n-1);
}

// Mutual recursion

void m2(unsigned x);

/*@ decreases n ; */
void m1(unsigned n){
  if(n != 0) m2(n-1);
}
/*@ decreases x ; */
void m2(unsigned x){
  if(x != 0) m1(x-1);
  if(x > 10) m2(x-1);

  (void)fact(x); // no verification of decreases here
}

// Mutual recursion failed

void missing_2(unsigned n);

/*@ decreases n ; */
void missing(unsigned n){
  if(n != 0) missing_2(n-1);
  if(n > 30) missing(n-1);
}

void missing_2(unsigned n){
  if(n != 0) missing(n-1);
}

// Mutual recursion + termination

void mt2(unsigned x);

/*@ terminates \true ;
    decreases n ; */
void mt1(unsigned n){
  if(n != 0) mt2(n-1);
}
/*@ terminates x <= 10 ;
    decreases x ; */
void mt2(unsigned x){
  if(x != 0) mt1(x-1);
  if(x > 10) mt2(x-1); // trivial verification of decreases here

  (void)fact(x); // no verification of decreases here
}

// Mutual recursion + wrong measure

/*@ predicate Wrong (integer old, integer new) = old > new && 0 <= old; */

void mw2(unsigned x);

/*@ decreases n for Rel ; */
void mw1(unsigned n){
  if(n != 0) mw2(n-1); // Wrong measure
}
/*@ decreases x for Wrong ; */
void mw2(unsigned x){
  if(x != 0) mw1(x-1); // Wrong measure
  if(x > 10) mw2(x-1);

  (void)fact(x); // no verification of decreases here
}

// Recursion with side-effect

int x ;

//@ decreases x ;
void se(void){
  if (x > 0){
    x -- ;
    se();
  }
}
