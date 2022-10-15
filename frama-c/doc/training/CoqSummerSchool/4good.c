void mean(int *p, int* q) {
  if (*p >= *q) { M = (*p - *q) / 2 + *q; }
  else { M = (*q - *p) / 2 + *p; }
}

