/* run.config
   OPT: -instantiate -then -pp-annot
*/

#include <string.h>

int foo(char* s1, char* s2, size_t len){
  return memcmp(s1, s2, len) ;
}
