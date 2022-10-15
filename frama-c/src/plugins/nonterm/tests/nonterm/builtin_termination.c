/* run.config
   STDOPT: #"-eva-builtin strlen:Frama_C_strlen"
 */

#include <string.h>

volatile int nondet;

int main() {
  char str1[4] = "ok";
  char str2[4];
  size_t len1, len2;
  str2[0] = 'o';
  str2[1] = 'k';  /* str2 not null-terminated */
  if (nondet) len1 = strlen(str1);
  if (nondet) len2 = strlen(str2); // str2 not a valid string =>
                                   // builtin does not terminate
  return 0;
}
