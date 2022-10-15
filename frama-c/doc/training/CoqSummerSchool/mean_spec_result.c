int M;
/*@
  requires \valid(p) && \valid(q);
  requires *p >= 0 && *q >= 0;
  assigns M;
  ensures M == (*p + *q) / 2;
*/
void mean(int* p, int* q) {
  if (*p >= *q) { M = (*p - *q) / 2 + *q;
  }
  else { M = (*q - *p) / 2 + *p;
  }
}
