/* run.config
 EXIT: 1
   OPT: -no-autoload-plugins -print
*/
void if_ghost_else_one_line_bad(int x, int y) {
  if (x) {
    x++;
  } //@ ghost else
  y++;
}
