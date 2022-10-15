/* run.config*
   STDOPT: #"-eva-msg-key d-multidim -eva-domains multidim -eva-plevel 1 -eva-multidim-disjunctive-invariants"
*/
#include "__fc_builtin.h"
#define N 4
#define M 4

typedef struct {
  float f;
  int i;
} t;

typedef struct {
  t t1[N];
  t t2[N];
} s;

/*@ axiomatic float_memory {
    predicate \are_finite(set<float> sf);
  }
*/

s z[M];

/*@ assigns z[..] \from \nothing;
    ensures \are_finite(z[..].t1[..].f) && \are_finite(z[..].t2[..].f);
  */
void f(void);

volatile int nondet;

void main1(s x) {
  s y1 = {{{{3.0}}}};
  s y2;

  if (nondet)
    y2.t1[0].f = 4.0;

  Frama_C_domain_show_each(x, y1, y2, z);

  /* The multidim domain wont infer anything except the structure from the
     assign: it considers x can contain anything including pointers, and thus no
     reduction is done by are_finite */
  //@ admit \are_finite(x.t1[..].f) && \are_finite(x.t2[..].f);
  Frama_C_domain_show_each(x);

  f();
  Frama_C_domain_show_each(z);  
  /* The multidim domain doesn't implement forward logic yet */
  //@ check \are_finite(z[..].t1[..].f) && \are_finite(z[..].t2[..].f);
}

void main2(void) {
  int t[10] = {0};
  for (int i = 0 ; i < 10 ; i++) {
    t[i] = 1;
  }
  //@ check t[0..9] == 1;
  Frama_C_domain_show_each(t);
}

void main3(void) {
  // Nest loops for 2d-arrays: currently the partitioning algorithm fails with it
  for (int i = 0 ; i < M ; i ++) {
    for (int j = 0 ; j < N ; j ++) {
      z[i].t1[j].f = 2.0;
      z[i].t1[j].i = 2;
    }
  }
  int a = Frama_C_interval(0,M-1);
  int b = Frama_C_interval(0,N-1);
  t r = z[a].t1[b];
  Frama_C_domain_show_each(z, r);
}

void main4(void) {
  // How trace partitioning changes array partitioning ?
  int t[N];

  //@ loop unroll 1;
  for (int i = 0; i < M; i++) {
    //@ loop unroll N;
    for (int j = 0; j < N; j++) {
      t[j] = 42;
    }
  }

  Frama_C_domain_show_each(t);
}

void main5(void) {
  // Array partitioning hints
  int t[20] = {0};

  //@ array_partition t, 0, 10, 20;
  for (int i = 0; i < 20; i++) {
    //@ split i >= 10;
    if (i < 10)
      t[i] = 1;
    else
      t[i] = 2;
  }

  Frama_C_domain_show_each(t);
}



void main6(void) {
  // Limit on the number of bounds in a segmentation
  int t[100];

  //@ loop unroll 100;
  for (int i = 0; i < 100; i++) {
    t[i] = 0;
  }

  Frama_C_domain_show_each(t);
}

typedef enum { INT=1, FLOAT=2 } type;

typedef struct {
  type typ;
  union {
    int i;
    float f; 
  } val;
} dynamic_typed;

void main7() {
  dynamic_typed t[1000];

  for (int i = 0 ; i < 1000 ; i++) {
    if (nondet) {
      t[i].typ = INT;
      t[i].val.i = 42;
    }
    else {
      t[i].typ = FLOAT;
      t[i].val.f = 42.0f;
    }
  }

  Frama_C_domain_show_each(t);

  int j = Frama_C_interval(0, 999);
  switch (t[j].typ) {
    case INT:
      Frama_C_show_each_INT(t[j].val.i);
      break;
    case FLOAT:
      Frama_C_show_each_FLOAT(t[j].val.f);
      break;
    default:
      Frama_C_show_each_BOTTOM("Unreachable");
      break;
  }
}

void main8(void) {
  int t[10] = {0};
  int *p = t;

  for (int i = 0 ; i < 10 ; i++) {
    *(p + i) = 1;
  }

  Frama_C_domain_show_each(t);
}

void main9(void) {
  int t1[10], t2[10];
  //@ eva_domain_scope multidim,t1;

  for (int i = 0 ; i < 10 ; i++) {

    t1[i] = 0;
    t2[i] = 0;
  }

  Frama_C_domain_show_each(t1, t2);
}


void main(s x) {
  main1(x);
  main2();
  main3();
  main4();
  main5();
  main6();
  main7();
  main8();
  main9();
}
