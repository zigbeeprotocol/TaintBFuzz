/*@ requires c == 0 && x == 1 ; */
void f(int x,...) /*@ ghost(int c) */ {
  /*@ ghost int g = c; */
}

/*@ requires c == 0 && x == 1 && y == 2; */
void g(int x, int y,...) /*@ ghost(int c) */ {
  /*@ ghost int g = c; */
}

void main(void){
  f(1) /*@ ghost(0) */;
  f(1, 2, 3) /*@ ghost(0) */;

  g(1, 2, 3, 4) /*@ ghost(0) */;
}
