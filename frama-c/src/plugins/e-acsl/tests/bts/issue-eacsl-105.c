/* run.config
   COMMENT: frama-c/e-acsl#105, test for delete block before exiting the 
    function in the presence of early return.
*/

int f() {
  int a = 10;
  goto lbl_1;

lbl_2:
  /*@ assert \valid(&a); */
  return 0;

lbl_1:
  goto lbl_2;
}

int main(void) {
  f();
  return 0;
}
