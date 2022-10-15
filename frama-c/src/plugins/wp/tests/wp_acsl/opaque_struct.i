/* run.config
   OPT: -wp-rte
*/
/* run.config_qualif
   OPT: -wp-rte
*/

struct S;

extern struct S S1;
extern struct S S2;

/*@ axiomatic test{
  @ check lemma fail: S1 == S2;
  @ check lemma succeed_L1: S1 == S1;
  @ check lemma succeed_L2: \block_length(&S1) >= 0;
}*/

/*@ assigns S1; */
void f(void);

void assigns(void){
  f();
  //@ check fail: S1 == \at(S1,Pre);
  //@ check succeed: S2 == \at(S2,Pre);
}

struct S* p ;

//@ assigns *p ;
void g(void);

/*@ requires \initialized(p);
    requires \valid(p);
*/
void initialized_assigns(void){
  g();
  //@ check fails: \initialized(p); // struct initialization not monotonic
  //@ check succeed: \block_length(p) >= 0;

  // while it can be proved in Coq, this is currently
  // too indirect for solvers.
  // @ check succeed: \block_length(p) >= \block_length(&S1);
}

/*@ requires ! \initialized(p); */
void uninitialized_assigns(void){
  g();
  /* NOTE:
     both shoud FAIL as we cannot prove that:
     - it is still uninitialized,
     - it has been initialized.
  */
  //@ check fail: ! \initialized(p);
  //@ check fail:   \initialized(p);
}

void assigned_via_pointer(void){
  g();
  //@ check fail: \at(*p, Here) == \at(*p, Pre);
}

//@ assigns *a ;
void assign(struct S *a);

//@ requires \separated(a, c);
void assigns_effect(int* p, float* q, char* c, struct S *a){
  assign(a);
  //@ check fail: *p == \at(*p, Pre);
  //@ check fail: *q == \at(*q, Pre);
  //@ check succeed: *c == \at(*c, Pre);
}

// regression on MemTyped chunk typing

void use(struct S * s);

//@ requires \valid(uc) && \valid_read(sc) ;
void chunk_typing(unsigned char* uc, signed char* sc){
  struct S* s ;
  *uc = *sc ;
  use(s) ;
}
