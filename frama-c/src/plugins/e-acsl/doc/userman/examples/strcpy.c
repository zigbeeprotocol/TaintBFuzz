#include <stdlib.h>
#include <string.h>

int main(void) {
  char *dst = malloc(sizeof(char) * 6);
  strcpy(dst, "foobar");
  return 0;
}
