/*@
  \only<1-4>??<requires \valid(p) && \valid(q);??>
  ensures ...
  assigns M;
  \only<3-4>??<\alert<3>??<terminates \true;??>??>
*/
void mean(int* p, int* q) {
  \only<2>??<while(1);??>\only<4>??<if (p == NULL || q == NULL) while(1); ??>
  if (*p >= *q) ... 
}
