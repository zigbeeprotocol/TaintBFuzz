/* run.config
   OPT:
   OPT: -wp-model real
*/
/* run.config_qualif
   OPT:
   OPT: -wp-model real
*/

/*@ assigns \nothing;
    ensures -0. <= sqrtf(x); */
void sqrtf(float x);

void test_sqrtf(float q){
  sqrtf(q);
  /*@ assert KO: \false; */
}

/*@ assigns \nothing;
    ensures -0. <= sqrt(x); */
void sqrt(double x);

void test_sqrt(double q){
  sqrt(q);
  /*@ assert KO: \false; */
}
