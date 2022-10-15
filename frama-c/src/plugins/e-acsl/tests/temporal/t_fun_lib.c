/* run.config
   COMMENT: Check handling library functions (without definitions)
*/

#include <limits.h>
#include <stdlib.h>

int main(void) {
  char *c = ".";
  /* Allocating function (such as malloc, recognized by name):
     - take block number of the returned pointer (after) */
  char *p = malloc(PATH_MAX), *q = NULL;
  q = malloc(PATH_MAX);

  /*@assert \valid(q) && \valid(p); */

  /* Function with no definition returning a pointer:
      same treatment as allocating function  */
  char *path = realpath(c, q);
  path = realpath(c, q);

  /*@assert \valid(path); */

  /* Function with no definition and no return value:
      do nothing */
  free(p);
  free(path);

  /*@assert ! \valid(p) && !\valid(path); */
  return 0;
}
