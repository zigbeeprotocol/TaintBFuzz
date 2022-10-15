/*@ 
    lemma div_pos: \forall integer i; 0<=i==> 0<=i/2<=i;
    lemma div_aux: \forall integer i,j; i/2 + j == (i+2*j)/2;

    logic integer div2(integer i) = i/2;
*/
unsigned int M;
int A;
/*@
  requires \valid(p) && \valid(q);
  assigns M;
  ensures M == div2(*p + *q);
*/
void mean(unsigned int* p, unsigned int* q) {
  if (*p >= *q) { M = (*p - *q) / 2 + *q; }
    else { M = (*q - *p) / 2 + *p; }
}

/*
Local Variables:
compile-command: "frama-c -jessie mean_spec.c"
End:
*/
