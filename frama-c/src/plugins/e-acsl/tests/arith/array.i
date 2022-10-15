/* run.config
   COMMENT: arrays
   STDOPT: #"-eva-slevel 5"
*/

int T1[3], T2[4];

void arrays() {
  // Pure logic arrays
  // (Unsupported at the moment by the kernel)
  // /*@ assert {[0] = 1, [1] = 2, [2] = 3} == {[0] = 1, [1] = 2, [2] = 3}; */
  // /*@ assert {[0] = 1, [1] = 2, [2] = 3} != {[0] = 4, [1] = 5, [2] = 6}; */
  // /*@ assert {[0] = 1, [1] = 2, [2] = 3} !=
  //     {[0] = 1, [1] = 2, [2] = 3, [3] = 4, [4] = 5, [5] = 6}; */

  // C arrays
  int a[] = {1, 2, 3};
  int b[] = {4, 5, 6};
  int c[] = {1, 2, 3};
  int d[] = {1, 2, 3, 4, 5, 6};
  /*@ assert a != b; */
  /*@ assert a == c; */
  /*@ assert a != d; */

  // Pointers to arrays
  int *e = a;
  int *f = b;
  int *g = c;
  int *h = a;
  /*@ assert e != f; */
  /*@ assert e != g; */
  /*@ assert e == h; */

  // Comparison between C arrays, logic arrays and pointer to arrays
  // /*@ assert a == {[0] = 1, [1] = 2, [2] = 3}; */ UNSUPPORTED by the kernel
  /*@ assert e == (int *) a; */
  /*@ assert e != (int *) c; */
  // /*@ assert (int[3])e == {[0] = 1, [1] = 2, [2] = 3}; */ UNSUPPORTED by the kernel
  // /*@ assert (int[])e == {[0] = 1, [1] = 2, [2] = 3}; */ UNSUPPORTED by the kernel
  /*@ assert a == (int[3])g; */
  /*@ assert a == (int[])g; */
  /*@ assert a != (int[3])f; */
  /*@ assert a != (int[])f; */

  // Comparison between sub-arrays
  int i[] = {1, 2, 3, 4, 5, 6};
  int j[] = {4, 5, 6, 1, 2, 3};
  int k[] = {4, 5, 6, 4, 5, 6};
  /*@ assert i != j; */
  /*@ assert i != k; */
  /*@ assert j != k; */
  int *l = &i[3];
  int *m = &j[3];
  int *n = &k[3];
  /*@ assert (int[3])l != (int[3])m; */
  /*@ assert (int[3])l == (int[3])n; */

  // Array truncation
  /*@ assert (int[3])i != (int[3])k; */
  /*@ assert (int[3])j == (int[3])k; */
  /*@ assert (int[2])l != (int[2])m; */
  /*@ assert (int[2])l == (int[2])n; */

  // Errors if trying an array extension
  /*ERROR assert (int[10])i != (int[10])k; */
  /*ERROR assert (int[10])j != (int[10])k; */
  /*ERROR assert (int[6])l != (int[6])m; */
  /*ERROR assert (int[6])l == (int[6])n; */

  // Errors while comparing a pointer to array with an array (logic or C)
  /*ERROR: assert e == a; */
  /*ERROR: assert e == {[0] = 1, [1] = 2, [2] = 3}; */

  // Error while casting a logic array to a pointer to array
  /*ERROR: assert e != (int*){[0] = 1, [1] = 2, [2] = 3}; */
}

void vlas(int n) {
  // FIXME: There is currently an error with the support of VLA in E-ACSL
  // https://git.frama-c.com/frama-c/e-acsl/-/issues/119

  // // Declare VLAs
  // int a[n+1];
  // int b[n+1];
  // int c[n+1];

  // // Initialize arrays
  // for (int i = 0; i < (n+1) ; ++i) {
  //     a[i] = i;
  //     b[i] = n + 1 - i;
  //     c[i] = i;
  // }

  // // // Compare VLAs
  // // // The naive comparison compare pointers
  // // /*@ assert a != b; */
  // // /*@ assert a == c; */
  // // // We need to cast to int[] to have an array comparison
  // // /*@ assert (int[])a != (int[])b; */
  // // /*@ assert (int[])a == (int[])c; */
}

int main(void) {

  for (int i = 0; i < 3; i++)
    T1[i] = i;
  for (int i = 0; i < 4; i++)
    T2[i] = 2 * i;

  /*@ assert T1[0] == T2[0]; */
  /*@ assert T1[1] != T2[1]; */

  arrays();
  vlas(3);

  return 0;
}
