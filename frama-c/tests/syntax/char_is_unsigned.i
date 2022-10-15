/* run.config
PLUGIN: rtegen
 MODULE: machdep_char_unsigned
   OPT: -print -machdep unsigned_char -then -constfold -rte
*/
char t[10];

void main() {
  int r = (t[0] == 'a');
  char c = 455;
}
