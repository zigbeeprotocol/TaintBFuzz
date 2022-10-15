/* run.config
 EXIT: 1
   OPT: -no-autoload-plugins -cpp-extra-args="-DERROR_LOC_WITH_COMMENTS"
 EXIT: 0
   OPT: -no-autoload-plugins -cpp-extra-args="-DALREADY_HAS_ELSE" -print -kernel-warn-key ghost:bad-use=feedback
 EXIT: 1
   OPT: -no-autoload-plugins -cpp-extra-args="-DBAD_ANNOT_POSITION"
*/
#ifdef ERROR_LOC_WITH_COMMENTS // Must check that the line indicated for undeclared "z" is correct
void if_ghost_else_block_comments_then_error(int x, int y) {
  if (x) {
    x++;
  } /*@ ghost
    // comment 1
    // comment 2
  else {
    y ++ ;
  } */

  z = 42;
}

#endif

#ifdef ALREADY_HAS_ELSE
// Must warn that the ghost else cannot appear since there is already a else
// Thus the ghost else is ignored and the resulting code does not comprise it

void if_ghost_else_block_bad(int x, int y) {
  if (x) {
    x++;
  } /*@ ghost else {
    y ++ ;
  } */
  else {
    y = 42;
  }
}

#endif

#ifdef BAD_ANNOT_POSITION // Syntax error because of the bad position of the annotation

void test(int x, int y){
  if(x){
    x++ ;
  } /*@ ghost
    //@ ensures \true ;
    else {
      y++ ;
    }
  */
}

#endif
