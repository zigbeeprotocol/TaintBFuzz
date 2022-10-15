/* run.config
   OPT:
   OPT: -wp-unfold-assigns -1
   OPT: -wp-unfold-assigns 2
   OPT: -wp-unfold-assigns 1
 */

/* run.config_qualif
   OPT: -wp-unfold-assigns -1
   OPT: -wp-unfold-assigns 2
   OPT: -wp-unfold-assigns 1
 */

struct S { int a,b; };

//@ assigns (*p) ;
void f(struct S *p);

//@ assigns p->a , p->b ;
void g(struct S *p);

//@ assigns s->a, s->b ;
void NO_UNFOLD_OK_1(struct S *s) {
  g(s);
}

//@ assigns (*s) ;
void NO_UNFOLD_OK_2(struct S *s) {
  f(s);
}

//@ assigns (*s) ;
void NO_UNFOLD_OK_3(struct S *s) {
  g(s);
}

//@ assigns s->a, s->b ;
void NO_UNFOLD_KO(struct S *s) {
  f(s);
}

/*@
  ensures \separated(p,q) ==> (*q == \old(*q));
  assigns (*p) ;
*/
void USE_ASSIGN_UNFOLD_OK(struct S *p , struct S *q)
{
  f(p);
}

/*@
  ensures \separated(p,q) ==> (*q == \old(*q));
  assigns p->a, p->b ;
*/
void USE_ASSIGN_UNFOLD_KO(struct S *p , struct S *q)
{
  f(p);
}

//@ assigns *s ;
void ASSIGN_NO_UNFOLD_OK(struct S *s) {
  struct S p = { 0,1 };
  *s = p ;
}

//@ assigns s->a, s->b ;
void ASSIGN_NO_UNFOLD_KO(struct S *s) {
  struct S p = { 0,1 };
  *s = p ;
}

/*@ assigns *(p+(0..n)); */
void f_assigns_range(int *p, unsigned n);

/*@ assigns *(p+0), *(p+(1..3)), *(p+4); */
void PARTIAL_ASSIGNS_STATIC(int *p) {
  f_assigns_range(p, 4);
}

/*@ requires n > 4 ;
    assigns *(p+0), *(p+(1..n-1)), *(p+n); */
void PARTIAL_ASSIGNS_VARS(int *p, unsigned n) {
  f_assigns_range(p, n);
}

struct With_array {
  int x ;
  int t [3] ;
};

//@ assigns *s ;
void f_assigns_with_array(struct With_array* s);

// FAILS AT UNFOLD LEVEL 1
//@ assigns s->x, s->t[0], s->t[1..2] ;
void NESTED_ARRAY_STATIC(struct With_array *s){
  f_assigns_with_array(s);
}

// FAILS AT UNFOLD LEVEL 1
/*@ requires n > 2 ;
    assigns s->x, s->t[0], s->t[1..n] ; */
void NESTED_ARRAY_VARS(struct With_array *s, unsigned n){
  f_assigns_with_array(s);
}

//@ assigns *(s+(0..n)) ;
void f_assigns_range_with_array(struct With_array* s, unsigned n);

// FAILS AT UNFOLD LEVEL 2
/*@ assigns s[0].x, s[0].t[0], s[0].t[1..2],
            s[1].x, s[1].t[0..2],
            s[2];
*/
void RANGE_NESTED_ARRAY_STATIC(struct With_array* s){
  f_assigns_range_with_array(s, 2);
}

// FAILS AT UNFOLD LEVEL 2
/*@ requires n > 2 && m > 3 ;
    assigns s[0].x, s[0].t[0], s[0].t[1..m],
            s[1].x, s[1].t[0..m],
            s[2 .. n];
*/
void RANGE_NESTED_ARRAY_VARS(struct With_array* s, unsigned n, unsigned m){
  f_assigns_range_with_array(s, n);
}
