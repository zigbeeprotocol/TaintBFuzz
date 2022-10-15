/* Tests for \object_pointer() */

void memvar(void)
{
  int x;
  //@check M1:  !\object_pointer(&x-1);
  //@check P0:   \object_pointer(&x);
  //@check P1:   \object_pointer(&x+1);
  //@check P2:  !\object_pointer(&x+2);
}

//@ logic char* GET = \null ;

void pointer(void)
{
  int x;
  int *p = &x ;
  *p = 1 ;
  //@check M1:  !\object_pointer(p-1);
  //@check P0:   \object_pointer(p);
  //@check P1:   \object_pointer(p+1);
  //@check P2:  !\object_pointer(p+2);
  //@check qed_NULL: \object_pointer(\null);
  //@check prover_NULL: \object_pointer(GET);
}

void array(void)
{
  int k;
  int a[25];
  int *q = &a[k];
  //@check ARR: (0 <= k <= 25) <==> \object_pointer(q);
}

struct S {
  int f ;
  int g ;
};

struct A {
  int m[10];
};

void compound(void)
{
  struct S u ;
  //@check M1: !\object_pointer(&u-1);
  //@check P0:  \object_pointer(&u);
  //@check P1:  \object_pointer(&u+1);
  //@check P2: !\object_pointer(&u+2);
  struct S s ;
  struct S *p = &s ;
  //@check F:   \object_pointer(&(p->f));
  //@check G:   \object_pointer(&(p->g));
  //@check F2:  \object_pointer(&(p->f)+2);
  //@check G2: !\object_pointer(&(p->g)+2);
  int k ;
  struct A a ;
  //@check AM: (0 <= k <= 10) <==> \object_pointer(&a.m[k]);
}
