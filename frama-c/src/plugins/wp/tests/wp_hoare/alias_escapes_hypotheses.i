/* run.config
   OPT:
   OPT:-wp-no-warn-memory-model -wp-check-memory-model -then -print
*/

/* run.config_qualif
  DONTRUN:
*/

int a ;

/*@ assigns \result \from \nothing ; */
int* f1(void){
  a = 42 ;
  return (void*) 0 ;
}

/*@ assigns \result \from &a ; */
int* f2(void){
  return &a ;
}

/*@ assigns \result \from \nothing ; */
int* f3(int x){
  return &x ;
}

/*@ assigns *p \from \nothing ; */
void fp1(int** p){
  a = 42 ;
  *p = (void*) 0 ;
}

/*@ assigns *p \from &a ; */
void fp2(int** p){
  *p = &a ;
}

/*@ assigns *p \from \nothing ; */
void fp3(int** p, int x){
  *p = &x ;
}
