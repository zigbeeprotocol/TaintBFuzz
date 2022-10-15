/* run.config
   OPT: -wp-definitions-terminate -wp-declarations-terminate
*/
/* run.config_qualif
   OPT: -wp-definitions-terminate -wp-declarations-terminate
*/

///// Simple recursion

//@ decreases n ;
void simpl_r(unsigned n){ // prove termination, warns unsupported decreases
  if(n) simpl_r(n-1);
}

void simpl_rf(unsigned n){ // fails termination
  if(n) simpl_rf(n-1);
}

///// Mutual recursion

// asks for decreases on both functions "mutual_"
void mutual_1(unsigned);
void mutual_2(unsigned);
// not part of the cluster, termination must succeed
void callee_no_r(void);

// fails termination (no decreases)
void mutual_1(unsigned n){
  if(n) mutual_2(n-1);
  callee_no_r();
}

// succeeds termination
//@ decreases n ;
void mutual_2(unsigned n){
  if(n) mutual_1(n-1); // fails decreases: no decreases for mutual_1
  simpl_rf(n); // this does not prevent termination proof
}

void callee_no_r(void){

}

// calls a cluster but not in cluster, termination must succeed
void caller_no_cluster(void){
  mutual_1(42);
}

///// Mutual recursion with function pointer

void fp(void (*)(unsigned), unsigned);

//@ decreases n ;
void function(unsigned n){
  if(n) fp(&function, n-1); // fails decreases: no decreases for fp
}

// termination fails : recursion without decreases
//@ requires pf == &function ;
void fp(void (*pf)(unsigned), unsigned n){
  if (n)
    //@ calls function ;
    (*pf)(n-1) ;
}
