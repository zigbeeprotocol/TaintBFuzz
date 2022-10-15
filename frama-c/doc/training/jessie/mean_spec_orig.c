//NOPP-BEGIN
/*@ lemma div_def: \forall integer i; 0<= i - 2*(i/2) <= 1; */
//NOPP-END
unsigned int M;
/*@
  requires \valid(p) && \valid(q);
  ensures M == (*p + *q) / 2;
*/
void mean(unsigned int* p, unsigned int* q) {
  if (*p >= *q) { M = (*p - *q) / 2 + *q; }
  else { M = (*q - *p) / 2 + *p; }
}

//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie-analysis -jessie-int-model exact -jessie-gui mean_spec.c"
End:
*/
//NOPP-END
