/* run.config
   OPT: -no-autoload-plugins -keep-comments -print
*/

void normal_only_if(int x, int y) {
  if (x) {
    x++;
  }
}

void normal_if_else(int x, int y) {
  if (x) {
    x++;
  } else {
    y++;
  }
}

void normal_if_else_intricated(int x, int y) {
  if (x)
    if (y)
      y++;
    else
      x++;
}

void if_ghost_else_one_line(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } //@ ghost else y ++ ;
}

void if_ghost_else_one_line_escaped(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } //@ ghost \
        else y ++ ;
}

void if_ghost_else_block(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } /*@ ghost else {
    y ++ ;
  } */
}

void if_ghost_else_multi_line_block(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } /*@ ghost else {
    y ++ ;
    y += x;
    -- y ;
  } */
}

void if_ghost_else_block_comments(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } /*@ ghost
    // comment 1
    // comment 2
  else {
    y ++ ;
  } */
}

void if_ghost_else_block_comments_escaped(int x) /*@ ghost(int y)*/ {
  if (x) {
    x++;
  } /*@ ghost
    // comment 1\
       continued
  else {
    y ++ ;
  } */
}

void normal_if_ghost_else_intricated(int x) /*@ ghost(int y)*/ {
  if (x)
    if (x)
      x++;
    //@ ghost else y++;
}

void ghost_else_plus_else_association(int x) /*@ ghost(int y)*/ {
  // we must take care to keep the "if" bloc when pretty-printing
  // as removing the brackets changes the program.
  if (x){
    if (x) x++ ;
    //@ ghost else y-- ;
  } else x ++ ;
}

void non_ghost_if_with_ghost_body(int x)  /*@ ghost(int y)*/ {
  // pretty-printer must take care of keeping the braces around the
  // single-(ghost)-statement blocks. Otherwise, the code is syntactically
  // invalid (empty, from a non-ghost point-of-view, then clause)
  if (x) { /*@ ghost y++; */ } else { /*@ ghost y--; */ }
}

void non_ghost_if_with_nop_ghost_body(int x)  /*@ ghost(int y)*/ {
  // pretty-printer must take care of keeping the braces around the
  // single-(ghost)-statement blocks. Even if the ghost statement is an
  // empty block!
  if (x) { /*@ ghost { } */ } else { /*@ ghost y++; */ }
}
