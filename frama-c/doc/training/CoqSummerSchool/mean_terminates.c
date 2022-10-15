/*@
  requires \valid(p) && \valid(q);
  ensures ...
  assigns M;
  \only<beamer:3| handout:1>??<terminates \true;??>
*/
void mean(int* p, int* q) {
  \only<beamer| beamer:2-3>??<while(1);??>
  \only<beamer:3| handout:1>??<if (p == NULL || q == NULL) while(1);??>
  if (*p >= *q) ...
}
