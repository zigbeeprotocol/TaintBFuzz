/* run.config_qualif
   OPT: -wp-auto wp:split
*/

struct S {
  int x ;
  int y ;
} ;
struct C {
  int x ;
  struct S s ;
  int a[10] ;
} ;

int x ;
int a[10] ;

struct C c ;
struct C ac [10];
//@ requires \initialized(&c) && \initialized(&ac);
void globals(void){
  // Simple type
  //@ check qed_ok: \initialized(&x) ;

  // Array type
  //@ check qed_ok: \initialized(&a) ;

  //@ check qed_ok: \initialized(&a[4]) ;
  //@ check qed_ko: \initialized(&a[10]) ;

  //@ check qed_ok: \initialized(&a[0 .. 9]) ;
  //@ check qed_ko: \initialized(&a[0 .. 10]) ;

  // Nested struct type
  //@ check qed_ok: \initialized(&c) ;
  //@ check qed_ok: \initialized(&c.s) ;
  //@ check qed_ok: \initialized(&c.s.y) ;

  //@ check provable: \initialized(&c.a) ;
  //@ check provable: \initialized(&c.a[4]) ;
  //@ check not_provable: \initialized(&c.a[10]) ;
  //@ check provable: \initialized(&c.a[0 .. 9]) ;
  //@ check qed_ko: \initialized(&c.a[0 .. 10]) ;

  // Complex accesses
  // OK
  //@ check qed_ok: \initialized(&ac[0]);
  //@ check qed_ok: \initialized(&ac[1].s);
  //@ check qed_ok: \initialized(&ac[2].s.y);
  //@ check qed_ok: \initialized(&ac[3].a);
  //@ check qed_ok: \initialized(&ac[4].a[5]);
  //@ check qed_ok: \initialized(&ac[1 .. 2]);
  //@ check provable: \initialized(&ac[2 .. 4].s);
  //@ check provable: \initialized(&ac[2 .. 6].s.y);
  //@ check provable: \initialized(&ac[3 .. 7].a);
  //@ check provable: \initialized(&ac[2 .. 9].a[5 .. 8]);

  // KO
  //@ check qed_ko: \initialized(&ac[10]);
  //@ check qed_ko: \initialized(&ac[10].a);
  //@ check qed_ko: \initialized(&ac[4].a[12]);
  //@ check qed_ko: \initialized(&ac[0 .. 10]);
  //@ check not_provable: \initialized(&ac[0 .. 10].s);
  //@ check not_provable: \initialized(&ac[0 .. 10].a);
  //@ check not_provable: \initialized(&ac[0 .. 9].a[0 .. 10]);
}

void locals(void){
  int x ;
  int a[2] ;

  struct C c ;

  //@ check qed_ok: !\initialized(&x);
  //@ check qed_ok: !\initialized(&a);
  //@ check qed_ok: !\initialized(&c);

  x = 1 ;
  //@ check qed_ok: \initialized(&x);

  a[0] = 1 ;
  //@ check qed_ok: \initialized(&a[0]);
  //@ check qed_ok: !\initialized(&a[1]);
  //@ check qed_ok: !\initialized(&a);

  a[1] = 2 ;
  //@ check qed_ok: \initialized(&a[0]);
  //@ check qed_ok: \initialized(&a[1]);
  //@ check provable: \initialized(&a);

  c.x = 1 ;
  //@ check qed_ok: \initialized(&c.x);
  //@ check qed_ok: !\initialized(&c.s);
  //@ check qed_ok: !\initialized(&c.a);
  //@ check qed_ok: !\initialized(&c);

  c.s.x = 1;
  //@ check qed_ok: \initialized(&c.s.x);
  //@ check qed_ok: !\initialized(&c.s.y);
  //@ check qed_ok: !\initialized(&c.s);
  //@ check qed_ok: !\initialized(&c);

  c.s.y = 1 ;
  //@ check qed_ok: \initialized(&c.s);
  //@ check qed_ok: !\initialized(&c);

  c.a[0] = c.a[1] = c.a[2] = c.a[3] = c.a[4] = c.a[5] = c.a[6] = c.a[7] = c.a[8] = 1;
  //@ check provable: \initialized(&c.a[0..8]) ;
  //@ check qed_ok: !\initialized(&c);

  c.a[9] = 1 ;
  //@ check qed_ok: \initialized(&c);
}

struct L {
  int x ;
  int f[10] ;
};

struct H {
  int x ;
  struct L l ;
  struct L al[5];
};

void complex_struct(void){
  struct H a;
  //@ check qed_ok: ! \initialized(&a);
  //@ check qed_ok: ! \initialized(&a);
  //@ check qed_ok: ! \initialized(&a.x);
  //@ check qed_ok: ! \initialized(&a.l);
  //@ check qed_ok: ! \initialized(&a.l.x);
  //@ check qed_ok: ! \initialized(&a.l.f);
  //@ check qed_ok: ! \initialized(&a.l.f[3]);
  //@ check qed_ok: ! \initialized(&a.l.f[1..6]);
  //@ check qed_ok: ! \initialized(&a.al);
  //@ check qed_ok: ! \initialized(&a.al[0]);
  //@ check qed_ok: ! \initialized(&a.al[0].x);
  //@ check qed_ok: ! \initialized(&a.al[0].f);
  //@ check qed_ok: ! \initialized(&a.al[0].f[7]);
  //@ check qed_ok: ! \initialized(&a.al[0].f[7 .. 9]);
  //@ check qed_ok: ! \initialized(&a.al[1..3]);
  //@ check qed_ok: ! \initialized(&a.al[1..3].x);
  //@ check qed_ok: ! \initialized(&a.al[1..3].f);
  //@ check qed_ok: ! \initialized(&a.al[1..3].f[7]);
  //@ check provable: ! \initialized(&a.al[1..3].f[7 .. 9]);
}
