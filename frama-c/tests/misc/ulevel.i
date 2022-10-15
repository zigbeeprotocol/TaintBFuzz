/* run.config
  PLUGIN: @EVA_PLUGINS@
  OPT: -then -ulevel-force -eva
 */

/* Tests the syntaxic loop unrolling when triggered by an option change
   (here -ulevel-force) and not at the first parsing. */

void main(void) {
  int i, j;
  /*@ loop pragma UNROLL 1; */
  for(i = 0; i < 4; i++)
    for(j = 0; j < 3; j++)
      ;
}
