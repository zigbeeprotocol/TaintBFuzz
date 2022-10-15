/*@ lemma div_ge: \forall integer i; i>=0 ==> 0<= i/2 <= i; 
 */
unsigned int M;

/*@ requires \valid(p) && \valid(q);
 */
void mean(unsigned int* p, unsigned int* q) {
  if (*p <= *q) M = (*q - *p) / 2 + *p;
  else M = (*p - *q) / 2 + *q;
}

/*
Local Variables:
compile-command: "frama-c -jessie mean.c"
End:
*/
