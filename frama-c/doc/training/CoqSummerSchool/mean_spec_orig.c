//NOPP-BEGIN
/*@ 
    lemma div_pos: \forall integer i; 0<=i==> 0<=i/2<=i;
    lemma div_aux: \forall integer i,j; i/2 + j == (i+2*j)/2;
*/
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
compile-command: "frama-c -jessie mean_spec.c"
End:
*/
//NOPP-END
