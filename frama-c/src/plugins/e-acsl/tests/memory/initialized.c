/* run.config
   COMMENT: Behaviours of the \initialized E-ACSL predicate
*/

#include <stdlib.h>

int A = 0;
int B;

#define ODD(_n) (_n % 2 != 0)

int main(void) {
  /* All globals are initialized, even if the initializer is not given */
  int *p = &A;
  int *q = &B;
  /*@assert \initialized(&A) ; */
  /*@assert \initialized(&B) ; */
  /*@assert \initialized(p) ;  */
  /*@assert \initialized(q) ;  */

  /* A local variable without an initializer is uninitialized */
  int a = 0;
  int b;
  long *r;
  long c[2] = {1, 1};
  long d[2];
  p = &a;
  q = &b;

  /*@assert \initialized(&a) ; */
  /*@assert ! \initialized(&b) ; */
  /*@assert \initialized(p) ; */
  /*@assert ! \initialized(q) ; */
  /*@assert \initialized(&c) ; */
  /*@assert ! \initialized(&d) ; */

  /* Local variables can also be initialized by assignments */
  b = 0;
  /*@assert \initialized(q);  */
  /*@assert \initialized(&b); */

  r = d;
  /*@assert ! \initialized(&d[0]); */
  /*@assert ! \initialized(d+1); */
  /*@assert ! \initialized(&d); */
  /*@assert ! \initialized(r); */
  /*@assert ! \initialized(r+1); */

  d[0] = 1;
  /*@assert \initialized(&d[0]); */
  /*@assert ! \initialized(d+1); */
  /*@assert ! \initialized(&d); */
  /*@assert \initialized(r); */
  /*@assert ! \initialized(r+1); */

  d[1] = 1;
  /*@assert \initialized(&d[0]); */
  /*@assert \initialized(d+1); */
  /*@assert \initialized(&d); */
  /*@assert \initialized(r); */
  /*@assert \initialized(r+1); */

  /* Malloc allocates un-initialized memory */
  p = (int *)malloc(sizeof(int *));
  /*@assert ! \initialized(p); */

  /* Calloc allocates initialized memory */
  q = (int *)calloc(1, sizeof(int));
  /*@ assert \initialized(q); */

  /* Block reallocared using `realloc' carries initialization of the
   * existing fragment but does not initialize the newly allocated one */
  q = (int *)realloc(q, 2 * sizeof(int));
  /*@assert \initialized(q); */
  q++;
  /*@assert ! \initialized(q); */
  q--;

  /* An initialized on an un-allocated region is always false. This does not
   * lead to undefined bevaviours in production mode or assertion failures in
   * debug mode. */
  free(p);
  free(q);
  /*@assert ! \initialized(p); */
  /*@assert ! \initialized(q); */

  /* Specially crafted calloc and realloc calls to check corner cases of
   * initialization */
  q = calloc(3, sizeof(int));
  /*@ assert \initialized(&q[0..2]); */
  q = realloc(q, 6 * sizeof(int));
  /*@ assert \initialized(&q[0..2]); */
  /*@ assert ! \initialized(&q[3]); */
  /*@ assert ! \initialized(&q[4]); */
  /*@ assert ! \initialized(&q[5]); */
  free(q);
  q = calloc(7, sizeof(int));
  /*@ assert \initialized(&q[0..6]); */
  q = realloc(q, 8 * sizeof(int));
  /*@ assert \initialized(&q[0..6]); */
  /*@ assert ! \initialized(&q[7]); */
  q = realloc(q, 10 * sizeof(int));
  /*@ assert \initialized(&q[0..6]); */
  /*@ assert ! \initialized(&q[7]); */
  /*@ assert ! \initialized(&q[8]); */
  /*@ assert ! \initialized(&q[9]); */
  free(q);
  q = calloc(2, sizeof(int));
  /*@ assert \initialized(&q[0..1]); */
  q = realloc(q, 4 * sizeof(int));
  /*@ assert \initialized(&q[0..1]); */
  /*@ assert ! \initialized(&q[2]); */
  /*@ assert ! \initialized(&q[3]); */
  free(q);
  q = calloc(6, sizeof(int));
  /*@ assert \initialized(&q[0..5]); */
  q = realloc(q, 3 * sizeof(int));
  /*@ assert \initialized(&q[0..2]); */
  free(q);
  q = malloc(6 * sizeof(int));
  /*@ assert ! \initialized(&q[0]); */
  /*@ assert ! \initialized(&q[1]); */
  /*@ assert ! \initialized(&q[2]); */
  /*@ assert ! \initialized(&q[3]); */
  /*@ assert ! \initialized(&q[4]); */
  /*@ assert ! \initialized(&q[5]); */
  q = realloc(q, 3 * sizeof(int));
  /*@ assert ! \initialized(&q[0]); */
  /*@ assert ! \initialized(&q[1]); */
  /*@ assert ! \initialized(&q[2]); */
  free(q);

  /* Spoofing access to a non-existing stack address */
  q = (int *)(&q - 1024 * 5);
  /*assert ! \initialized(q); */

  /* Spoofing access to a non-existing global address */
  q = (int *)128;
  /*@assert ! \initialized(q); */

  p = NULL;
  /*@assert ! \initialized(p); */

  /* Partial initialization */
  int size = 100;
  char *partsc = (char *)malloc(size * sizeof(char));
  char *partsi = (char *)malloc(size * sizeof(int));

  for (int i = 0; i < size; i++) {
    if (ODD(i))
      partsc[i] = '0';
    else
      partsi[i] = 0;
  }

  for (int i = 0; i < size; i++) {
    if (ODD(i)) {
      /* @assert \initialized(partsc + i);   */
      /* @assert ! \initialized(partsi + i); */
    } else {
      /* @assert \initialized(partsi + i);   */
      /* @assert ! \initialized(partsc + i); */
    }
  }

  /* Check duplicate initialization does not affect correct count of
   * initialized bits (relevant for bittree model). */
  int dup[2];
  dup[0] = 1;
  dup[0] = 1;
  /* @assert ! \initialized(&dup); */
}
