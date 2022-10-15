/* run.config
   OPT:-wp-model +ref -wp-no-warn-memory-model -wp-check-memory-model -then -print
*/

/* run.config_qualif
   OPT:-wp-model +ref -wp-no-warn-memory-model -wp-check-memory-model
*/

int g ;

//@ assigns \nothing ;
int sep(int* p){
  return *p + g;
}

//@ assigns \nothing;
void call_sep_ok(void){
  int l = 42;
  sep(&l);
}

//@ assigns \nothing ;
void call_sep_bad_sep(void){
  sep(&g);
}

//@ assigns \nothing ;
void call_sep_bad_valid(void){
  int * p ;
  {
    int l ;
    p = &l ;
  }
  sep(p);
}

int *p;
//@ assigns \nothing ;
int gptr_sep(void){
  return *p + g;
}

//@ assigns p \from \nothing ;
void call_gptr_sep_ok(void){
  int l = 42;
  p = &l ;
  gptr_sep();
}

//@ assigns p \from &g ;
void call_gptr_sep_bad(void){
  p = &g;
  gptr_sep();
}


/*@ assigns *p ; */
void assigns_ptr(int *p){
  *p = g + 42 ;
}

//@ assigns \nothing;
void call_assigns_ptr_ok(void){
  int l = 42;
  assigns_ptr(&l);
}

//@ assigns g ;
void call_assigns_ptr_bad(void){
  assigns_ptr(&g);
}

/*@
  assigns \result \from p ;
  assigns *p ;
  ensures \result == p ;
*/
int * add_return_ok(int *p){
  (*p) += g ;
  return p ;
}

//@ assigns g ;
void call_add_return_ok(void){
  int l = 0;
  int *p = add_return_ok(&l);
  *p = 0;
}

//@ assigns g ;
void call_add_return_bad(void){
  int *p = add_return_ok(&g);
  *p = 0;
}

//@ assigns \result \from &x ;
int * bad_return_formal(int x){
  return &x;
}
