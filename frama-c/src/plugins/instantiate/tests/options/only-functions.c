/* run.config
  STDOPT: +"-instantiate-fct=foo"
*/

#include <string.h>

void foo(){
  int src[10] = {0} ;
  int dest[10] ;
  memcpy(dest, src, sizeof(src)) ;
}

void bar(){
  int src[10] = {0} ;
  int dest[10] ;
  memcpy(dest, src, sizeof(src)) ;
}

void baz(){
  int src[10] = {0} ;
  int dest[10] ;
  memcpy(dest, src, sizeof(src)) ;
}
