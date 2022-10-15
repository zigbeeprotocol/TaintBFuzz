/* run.config
 COMMENT: Test `strcat` and `strncat` E-ACSL built-ins
 DEPS: @PTEST_DEPS@ utils/signalled.h
   STDOPT: +"-eva-precision=1"
 COMMENT: This part is blank on purpose (test stability + Dune)




*/

#include "utils/signalled.h"
#include <stdlib.h>
#include <string.h>

void test_memory_tracking() {
  {
    char dest[4];
    strcpy(dest, "a");
    char src[] = "b";
    //@ assert \initialized(&dest[0..1]);
    //@ assert !\initialized(&dest[2..3]);
    //@ assert \initialized(&src[0..1]);

    strcat(dest, src);
    //@ assert \initialized(&dest[0..2]);
    //@ assert !\initialized(&dest[3]);
  }
  { // strncat with n < strlen(src)
    char dest[4];
    strcpy(dest, "a");
    char src[] = "bc";
    //@ assert \initialized(&dest[0..1]);
    //@ assert !\initialized(&dest[2..3]);
    //@ assert \initialized(&src[0..2]);

    strncat(dest, src, 1);
    //@ assert \initialized(&dest[0..2]);
    //@ assert !\initialized(&dest[3]);
  }
  { // strncat with n >= strlen(src)
    char dest[4];
    strcpy(dest, "a");
    char src[] = "b";
    //@ assert \initialized(&dest[0..1]);
    //@ assert !\initialized(&dest[2..3]);
    //@ assert \initialized(&src[0..1]);

    strncat(dest, src, 2);
    //@ assert \initialized(&dest[0..2]);
    //@ assert !\initialized(&dest[3]);
  }
}

int main(int argc, const char **argv) {
  char *const_str = "abcd";
  char *unalloc_str = malloc(5);
  char *_barrier = malloc(1);
  char *empty_str = "";
  free(unalloc_str);
  {
    /* strcat */
    char dest1[9] = "dcba";
    char dest2[8] = "dcba";
    char dest3[5] = "----";
    char dest4[10] = "dcba";
    char *pd1 = &dest1;
    char *pd2 = &dest2;
    char *pd3 = &dest3;
    char *pd4 = &dest4;

    /* strcat */
    OK(strcat(dest1, const_str)); // enough space in dest [ok]
    // enough space in dest (concat with empty) [ok]:
    OK(strcat(dest3, empty_str));
    ABRT(strcat(dest2, const_str));       // insufficient space in dest [abort]
    ABRT(strcat(unalloc_str, const_str)); // unallocated in dest [abort]
    ABRT(strcat(dest2, unalloc_str));     // unallocated in src [abort]
    ABRT(strcat(NULL, ""));               // NULL in dest [abort]
    ABRT(strcat(dest1, NULL));            // NULL in src [abort]
    ABRT(strcat(const_str, const_str));   // immutable in dest [abort]
    ABRT(strcat(pd1, pd1));     // overlapping spaces (same address) [abort]
    ABRT(strcat(pd1 + 3, pd1)); // overlapping spaces [abort]
    ABRT(strcat(pd4 + 4, pd4)); // overlapping spaces [abort]
    OK(pd4[5] = '\0'; strcat(pd4 + 5, pd4)); // non-overlapping
  }
  {
    /* strncat */
    char dest1[9] = "dcba";
    char dest2[8] = "dcba";
    char dest3[5] = "----";
    char dest4[10] = "dcba";
    char *pd1 = &dest1;
    char *pd2 = &dest2;
    char *pd3 = &dest3;
    char *pd4 = &dest4;
    /* strncat */
    OK(strncat(dest1, const_str, 4));         // enough space in dest
    ABRT(strncat(dest2, const_str, 4));       // insufficient space in dest
    ABRT(strncat(unalloc_str, const_str, 1)); // unallocated in dest [abort]
    ABRT(strncat(dest2, unalloc_str, 1));     // unallocated in src [abort]
    ABRT(strncat(NULL, const_str, 1));        // NULL in dest [abort]
    ABRT(strncat(dest2, NULL, 1));            // NULL in src [abort]
    ABRT(strncat(const_str, const_str, 1));   // immutable in dest [abort]

    ABRT(strncat(pd1, pd1, 1));     // overlapping spaces (same address) [abort]
    ABRT(strncat(pd1 + 3, pd1, 5)); // overlapping spaces [abort]
    ABRT(strncat(pd4 + 4, pd4, 5)); // overlapping spaces [abort]
  }
  test_memory_tracking();
  return 0;
}
