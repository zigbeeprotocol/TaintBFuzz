/* run.config
   COMMENT: frama-c/e-acsl#172, test for a term with two successive logic
   coercion.
*/
double d2 = 11.;
int main() {
  //@ assert (int)d2 > 10;
  return 0;
}
