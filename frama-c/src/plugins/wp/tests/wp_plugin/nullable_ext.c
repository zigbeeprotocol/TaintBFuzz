/* run.config
   OPT: -wp-model Caveat
   EXIT: 1
   OPT: -cpp-extra-args="-DFAIL_1"
   EXIT: 1
   OPT: -cpp-extra-args="-DFAIL_2"
   EXIT: 1
   OPT: -cpp-extra-args="-DFAIL_3"
   EXIT: 1
   OPT: -cpp-extra-args="-DFAIL_4"
*/
/* run.config_qualif
   OPT: -wp-model Caveat
*/

int x;
int *g;

/*@ assigns *g, *p, x ;
    wp_nullable_args p ;
*/
void nullable_coherence(int *p) {
  if (p == (void *)0) {
    //@ check must_fail: \false ;
    return;
  }
  //@ check \valid(p);
  *p = 42;
  *g = 24;
  x = 1;
}

/*@ assigns *p, *q, *r, *s, *t ;
    wp_nullable_args p, q, r ;
*/
void nullable_in_context(int *p, int *q, int *r, int *s, int *t) {
  *p = 42;
  *q = 42;
  *r = 42;
  *s = *t = 0;
}

/*@ assigns *ptr ;
    wp_nullable_args ptr  ;
*/
void with_declaration(int *ptr);
void with_declaration(int *ptr) {}

#ifdef FAIL_1
/*@ assigns *ptr ;
    wp_nullable_args unexisting_ptr ;
*/
void fails_no_variable(int *ptr) {}
#endif

#ifdef FAIL_2
/*@ assigns *ptr ;
    wp_nullable_args *ptr ;
*/
void not_a_variable(int *ptr) {}
#endif

#ifdef FAIL_3
/*@ assigns *ptr ;
    wp_nullable_args g ;
*/
void not_a_formal(int *ptr) {}
#endif

#ifdef FAIL_4
/*@ assigns x ;
    wp_nullable_args f ;
*/
void not_a_pointer(int f) {}
#endif
