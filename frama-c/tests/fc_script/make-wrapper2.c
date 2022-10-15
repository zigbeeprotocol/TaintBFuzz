/* run.config
   DONTRUN: part of the test in make-wrapper.c
*/

int defined(int a) {
  return a + 1;
}

/*@
  assigns \result \from a;
  ensures \result == a + 2;
 */
int specified(int a);

// defined in another, non-included, file
int external(int a);
