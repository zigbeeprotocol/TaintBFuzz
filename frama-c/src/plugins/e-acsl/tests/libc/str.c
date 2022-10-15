/* run.config
   COMMENT: Test non built-in `strcpy`, `strncpy`, `strcat` and `strncat` memory
   COMMENT: tracking
*/

#include <string.h>

int main() {
  {
    char dest[4];
    char src[] = "b";
    //@ assert !\initialized(&dest[0..3]);
    //@ assert \initialized(&src[0..1]);

    strcpy(dest, src);
    //@ assert \initialized(&dest[0..1]);
    //@ assert !\initialized(&dest[2..3]);
  }
  { // strncpy with n < strlen(src)
    char dest[4];
    char src[4] = "ab";
    //@ assert !\initialized(&dest[0..3]);
    //@ assert \initialized(&src[0..3]);

    strncpy(dest, src, 1);
    //@ assert \initialized(&dest[0]);
    //@ assert !\initialized(&dest[1..3]);
  }
  { // strncpy with n >= strlen(src)
    char dest[4];
    char src[4] = "b";
    //@ assert !\initialized(&dest[0..3]);
    //@ assert \initialized(&src[0..3]);

    strncpy(dest, src, 3);
    //@ assert \initialized(&dest[0..2]);
    //@ assert !\initialized(&dest[3]);
  }
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
  return 0;
}
