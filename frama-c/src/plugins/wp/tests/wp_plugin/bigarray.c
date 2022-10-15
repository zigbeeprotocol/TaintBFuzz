/* run.config
   EXIT: 0
   OPT: -cpp-extra-args="-DFIT"
   EXIT: 1
   OPT: -cpp-extra-args="-DLARGE"
 */

/* run.config_qualif
   DONTRUN:
*/

#include <stdint.h>
#ifdef FIT
#define SIZE (SIZE_MAX / sizeof(int))
#endif
#ifdef LARGE
#define SIZE SIZE_MAX
#endif

/*@
  assigns \result \from p[0..n-1];
*/
int f(int *p, int n)
{
  int s = 0;
  int tmp[SIZE];
  /*@ loop assigns i,s, tmp[..]; */
  for (int i = 0; i < n; i++) {
    s+= p[i]; tmp[i] = s;
  }
  return s;
}
