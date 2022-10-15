void if_ghost_else_one_line(int x) /*@ ghost (int y) */ {
  if (x) {
    x++;
  } //@ ghost else y ++ ;
}

void if_ghost_else_block(int x) /*@ ghost (int y) */ {
  if (x) {
    x++;
  } /*@ ghost else {
    y ++ ;
  } */
}

void if_ghost_else_multi_line_block(int x) /*@ ghost (int y) */ {
  if (x) {
    x++;
  } /*@ ghost else {
    y ++ ;
    y += x;
    -- y ;
  } */
}

void normal_if_ghost_else_intricated(int x) /*@ ghost (int y) */ {
  if (x)
    if (x)
      x++;
    //@ ghost else y++;
}

void ghost_else_plus_else_association(int x) /*@ ghost (int y) */ {
  // we must take care to keep the "if" bloc when pretty-printing
  // as removing the brackets changes the program.
  if (x){
    if (x) x++ ;
    //@ ghost else y-- ;
  } else x ++ ;
}
