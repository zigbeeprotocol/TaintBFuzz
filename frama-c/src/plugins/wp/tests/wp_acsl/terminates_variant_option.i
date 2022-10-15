/* run.config
   OPT:
   OPT: -wp-variant-with-terminates
*/
/* run.config_qualif
   OPT:
   OPT: -wp-variant-with-terminates
*/

// -wp-variant-with-terminates <--- default to FALSE


//@ terminates *p >= 0 ;
void fails_positive(int *p){
  /*@ loop invariant \at(*p, Pre) >= 0 ==> 0 <= *p <= \at(*p, Pre) ;
      loop assigns *p ;
      loop variant *p ;
  */
  while(*p)
    --(*p);
}

//@ terminates !keep_going ;
void fails_decreases(int keep_going){
  unsigned i = 100;
  /*@ loop assigns i;
      loop variant i;
  */
  while(i > 0){
    if(! keep_going) i-- ;
  }
}

//@ terminates c1 != 0;
void f1 (int c1, int c2) {
  int cpt = c1 ;
  /*@ loop invariant c1 >= 0 ==> 0 <= cpt <= c1 ;
    @ loop assigns cpt ;
    @ loop variant cpt ;
    @*/
  while (1) {
    if (c1 || c2) {
      cpt --;
      if (cpt <= 0) break;
    }
  }
}

//@ terminates \false ;
void trivial_variant(void){
  /*@ loop assigns \nothing ;
      loop variant -1 ;
  */
  while(1);
}

void trivial_variant_default(void){
  /*@ loop assigns \nothing ;
      loop variant -1 ;
  */
  while(1);
}
