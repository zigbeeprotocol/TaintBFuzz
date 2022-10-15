/* run.config
   OPT: -wp-model Caveat
*/
/* run.config_qualif
   OPT: -wp-model Caveat
*/

int x ;
int *g ;

/*@ assigns *g, *p, x ; */
void nullable_coherence(int* p /*@ wp_nullable */){
  if(p == (void*)0){
    //@ check must_fail: \false ;
    return;
  }
  //@ check \valid(p);
  *p = 42;
  *g = 24;
  x = 1;
}

//@ assigns *p, *q, *r, *s, *t ;
void nullable_in_context
(int* p /*@ wp_nullable */,
 int* q /*@ wp_nullable */,
 int* r /*@ wp_nullable */,
 int* s, int* t)
{
  *p = 42;
  *q = 42;
  *r = 42;
  *s = *t = 0;
}
