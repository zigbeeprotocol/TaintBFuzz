/* run.config
  OPT:  -wp-model eva1
  OPT:  -wp-model eva2
*/

/* run.config_qualif
  OPT:  -wp-model eva1
  OPT:  -wp-model eva2
*/

#include "__fc_builtin.h"

/*@
  axiomatic P {
    predicate P(int x);
  }

 @*/

int z;

void f (int *x, int *y){
  if(z==41) return;
  *x = *x+1;
  /*@ assert P(*x) && P(*y) && P(z); @*/
  int r = 1/(*x-42);
}

void g (int *x, int *y){
  *x = *x+1;
  /*@ assert P(*x) && P(*y) && P(z); @*/
}

void h (int *x, int *y){
  /*@ assert *x == *y; */
}

void h2 (int *x, int *y, int *z){
  *x = *z;
  *y = 1;
  /*@ assert *x == *z; */
}

void main(){
  int x = Frama_C_interval(2,1000);
  int y = Frama_C_interval(2,1000);
  z = Frama_C_interval(2,1000);
  f(&z,&z);
  g(&x,&y);
  h(&x,&x);
  h2(&x,&y,&z);
}
