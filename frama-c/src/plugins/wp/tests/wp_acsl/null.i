
//@ ensures \result == 0;
int null_is_zero (void) {
  void * p = (void*)0;
  return (int) p;
}

/*@ lemma qed_not_valid_null:      !\valid     ((char *)\null); */
/*@ lemma qed_not_valid_read_null: !\valid_read((char *)\null); */

/*@ logic char* GET = \null ; */
/*@ lemma prover_not_valid_null:      !\valid     ((char *)GET); */
/*@ lemma prover_not_valid_read_null: !\valid_read((char *)GET); */


// Prove null invalidity:

//@ assigns *p;
void qed_f(char *p);

/*@ assigns \nothing; */
void qed(){
  qed_f(0);
}

//@ assigns *p;
void prover_f(char *p);

/*@ requires x == GET;
    assigns \nothing; */
void prover(char *x){
  prover_f(x);
}
