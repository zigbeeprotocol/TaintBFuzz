/* run.config
  OPT: -wp-prop=OK,FAIL
*/
/* run.config_qualif
  OPT: -wp-prop=OK,FAIL
*/

struct S {
  int i ;
  int a[10] ;
};

void atomic(int* ptr){
  /*@ loop assigns i, *ptr; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(ptr);
}

void comp(struct S* s){
  /*@ loop assigns i, *s; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(s);
}

void array(int (* array) [10]){
  /*@ loop assigns i, (*array)[0..9]; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(array);
}

int glob_atomic ;
int * pg_atomic = &glob_atomic ;
int * const cg_atomic = &glob_atomic ;

void assigned_glob_atomic(void){
  /*@ loop assigns i, *pg_atomic, *cg_atomic; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(pg_atomic);
  //@ check OK: \initialized(cg_atomic);
}

struct S glob_comp ;
struct S * pg_comp = &glob_comp ;
struct S * const cg_comp = &glob_comp ;

void assigned_glob_comp(void){
  /*@ loop assigns i, *pg_comp, *cg_comp; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(pg_comp);
  //@ check FAIL: \initialized(cg_comp); // struct not initialized by default
}

int glob_array[10] ;
int (* pg_array) [10] = &glob_array ;
int (* const cg_array) [10] = &glob_array ;

void assigned_glob_array(void){
  /*@ loop assigns i, (*pg_array)[0 .. 9], (*cg_array)[0 .. 9]; */
  for(int i = 0; i < 10; ++i){}
  //@ check FAIL: \initialized(pg_array);
  //@ check OK: \initialized(cg_array);
}
