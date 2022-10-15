/*@
  requires \valid(p) && \valid(q);
  ensures M == (*p + *q) / 2;
  \only<handout| handout:2>??<ensures *p == \action<alert@2>??<\old(*p)??> && *q == \action<alert@2>??<\old(*q)??>;??>\only<1|handout:3>??<\action<handout:alert@3>??<assigns M??>;??>
*/
void mean(unsigned int* p, unsigned int* q);
