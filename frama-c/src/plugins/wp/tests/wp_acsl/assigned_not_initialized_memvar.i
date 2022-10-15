/* run.config
  OPT: -wp-prop=FAIL
*/
/* run.config_qualif
  OPT: -wp-prop=FAIL
*/

struct S {
  int i ;
  int a[10] ;
};

void atomic(void){
  int x ;
  /*@ loop assigns i, x; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(&x);
}

void comp(void){
  struct S s ;
  /*@ loop assigns i, s; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(&s);
}

void array(void){
  int array[10];
  /*@ loop assigns i, array[0..9]; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(&array);
}
