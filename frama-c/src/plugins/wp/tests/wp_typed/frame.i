struct { int f; int *ptr; } comp[20] ;

int *Q ;

//@ requires 0 <= k < 20 ;
void compound(int k) {
  int m = 1;
  Q = &m ; // alias taken on m
  *comp[k].ptr = 4 ;
  //@ assert SEP: \separated(comp[k].ptr,&m);
  //@ assert RES: m == 1;
}

// NOTE:
// if we require \valid(comp[k].ptr) the goal is provable without frame conditions
// since it can not be aliased with 'm' at PRE, which is not (yet) valid.

// For those two examples, we want the assert false to fail:
//  -> the frame condition must *not* introduce incoherence on initialization

void local_region(void) {
  char b[4] = {0};
  char *x = b ;
  char **in_memtyped = &x ; // be sure to put x in MemTyped
  //@ assert A:X: \valid_read(x + (0..3));
  //@ assert A:Y: \false ;
}

struct S { char b ; };

void formal_region(struct S s) {
  char *x = &s.b ;
  char **in_memtyped = &x ; // be sure to put x in MemTyped
  //@ assert A:X: \valid_read(x);
  //@ assert A:Y: \false ;
}
