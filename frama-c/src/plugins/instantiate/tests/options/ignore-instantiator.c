/* run.config
  STDOPT:+"-instantiate-no-memcpy"
*/

#include <string.h>

void foo(){
  int src[10] ;
  int dest[10] ;
  memset(src, 0, sizeof(src)) ;
  memcpy(dest, src, sizeof(src)) ;
}
