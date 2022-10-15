/* run.config
OPT: -kernel-warn-key=annot-error=active
*/

typedef double typetab[2];

double f(typetab *t);

int x;

//@ assigns \result \from x;
double annotations_to_accept(typetab *t) {
  //@ requires r0: \valid( t ) ;
  //@ requires r1: \valid( &*t ) ;
  //@ requires r2: \valid( (&*t) + (0..0) ) ;
  //@ requires r3: \valid( ((double *)t) + (0..1) ) ;
  //@ behavior b3: assigns ((double *)t)[0..1];
  return f(t);
}

/*@ behavior acc_0: assigns \result \from &x ;
    behavior acc_1: assigns \result \from &f ;
*/
int * from_address_to_accept(int f){
  return (void*)0 ;
}


int g(void);

//@ logic int lx = (int)0;

extern typetab *t;

//@ ensures to_reject: \fresh{Pre,Here}(&\result,sizeof(\result));
int annotations_to_reject(void) {
  //@ behavior to_reject_b0: assigns *t;
  //@ behavior to_reject_b1: assigns t[0];
  //@ behavior to_reject_b2: assigns (&*t)[0..0];
  //@ behavior to_reject_0: assigns (int)x;
  //@ behavior to_reject_1: assigns (char)x;
  //@ behavior to_reject_2: assigns *(int *)(&(char)x);
  //@ behavior to_reject_3: assigns;
  //@ behavior to_reject_4: requires \valid(&\empty);
  //@ behavior to_reject_5: assigns lx;
  //@ behavior to_reject_6: assigns x \from lx;
  return g();
}

/*@ behavior rej_0: assigns \result \from &l ; */
int * from_address_to_reject(int f){
  int l ;
  //@ behavior rej_1: assigns l \from &lx ;
  return (void*)0 ;
}

typedef struct _M {
  int x;
} M;

struct N {
  int y;
};

//@ model M { struct N z; };
//@ model M { int t; };

M m;

//@ requires x == &m.t;
void refuse_address_of_model_field(int* x);

//@ requires x == &m.z.y;
void refuse_subfield_of_model_field(int* x);
