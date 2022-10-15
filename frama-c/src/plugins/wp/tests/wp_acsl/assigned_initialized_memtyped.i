/* run.config
  OPT: -wp-prop=CHECK,FAILS
*/
/* run.config_qualif
  OPT: -wp-prop=CHECK,FAILS
*/

struct S {
  int i ;
  int a[10] ;
};

void initialize(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant CHECK: 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns CHECK: i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  //@ check CHECK: \initialized(s);
}

void range(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@ loop assigns CHECK: i, s->a[1 .. 4]; */
  for(int i = 0; i < 10; ++i){
    if(1 <= i && i <= 4) s->a[i] = 1 ;
  }
  //@ check FAILS: \initialized(s); // memtyped assigns not monotonic
}

void field(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@ loop assigns CHECK: i, s->i; */
  for(int i = 0; i < 10; ++i){
    s->i++;
  }
  //@ check FAILS: \initialized(s); // memtyped assigns not monotonic
}

void array(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@
    loop invariant 0 <= i <= 10;
    loop assigns CHECK: i, s->a[0..9];
  */
  for(int i = 0; i < 10; ++i){
    s->a[i] = 1 ;
  }
  //@ check FAILS: \initialized(s); // memtyped assigns not monotonic
}

void index(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@ loop assigns CHECK: i, s->a[4]; */
  for(int i = 0; i < 10; ++i){
    if(i == 4) s->a[i] = 1 ;
  }
  //@ check FAILS: \initialized(s);  // memtyped assigns not monotonic
}

void descr(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@ loop assigns CHECK: i, { s->a[i] | integer i ; i \in { 0, 2, 4 } }; */
  for(int i = 0; i < 10; ++i){
    if(i == 0 || i == 2 || i == 4) s->a[i] = 1 ;
  }
  //@ check FAILS: \initialized(s);  // memtyped assigns not monotonic
}

void comp(struct S* s){
  s->i = 0 ;
  /*@
    loop invariant 0 <= i <= 10 && \initialized(&s->a[0 .. i-1]);
    loop assigns i, s->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) s->a[i] = 0;

  /*@
    loop invariant 0 <= i <= 10 ;
    loop assigns CHECK: i, *s;
  */
  for(int i = 0; i < 10; ++i){
    s->a[i] = 1 ;
    s->i++;
  }
  //@ check FAILS: \initialized(s); // memtyped assigns not monotonic
}

struct S glob ;
struct S * pg = &glob ;
struct S * const cg = &glob ;

void assigned_glob(void){
  //@ check FAILS: \initialized(cg); // no default init for structs
  pg->i = 0;
  /*@
    loop invariant CHECK: 0 <= i <= 10 && \initialized(&pg->a[0 .. i-1]);
    loop assigns CHECK: i, pg->a[0 .. 9];
  */
  for(int i = 0; i < 10; ++i) pg->a[i] = 0;

  /*@
    loop invariant 0 <= i <= 10 ;
    loop assigns CHECK: i, *pg;
  */
  for(int i = 0; i < 10; ++i){
    pg->a[i] = 1 ;
    pg->i++;
  }
  //@ check FAILS: \initialized(pg); // memtyped assigns not monotonic
  //@ check FAILS: \initialized(cg); // no default init for structs
}
