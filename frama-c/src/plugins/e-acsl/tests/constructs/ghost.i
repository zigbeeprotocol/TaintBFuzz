/* run.config
   COMMENT: ghost code
*/

/*@ ghost int G = 0; */
/*@ ghost int \ghost *P; */

// /*@ ghost int foo(int *x) { return *x + 1; } */

int main(void) {
  /*@ ghost P = &G; */;
  /*@ ghost int \ghost *q = P; */
  /*@ ghost (*P)++; */
  /*@ assert *q == G; */
  //  /*@ ghost G = foo(&G); */
  //  /*@ assert G == 2; */

  int x = 1;
  if (x) {
    x++;
  } /*@ ghost else {
    G++ ;
    G++ ;
  }*/
}
