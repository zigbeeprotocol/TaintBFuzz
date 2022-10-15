char * f(void);
void g(void) {
  struct capture* b = f();
  //@ assert \valid(b);
}
