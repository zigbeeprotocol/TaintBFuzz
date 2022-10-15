/* run.config
   EXIT: 1
   STDOPT:
*/
/* run.config_qualif
   DONTRUN:
*/

/*@ predicate P{L}(int* a) = *a == 42 ; */

void merge(void) {
  int tmp[0xFFFFFFFFFFFFFFFFULL];
  //@ loop invariant sorted: P(&tmp[0]);
  while(1){}
}
