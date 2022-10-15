#include <stdio.h>

int main(){
  FILE *stream;
  char *format;
  char *str;
  size_t size;

  fprintf(stream, format, 1, "2", 3);
  printf(format, 1, "2", 3);
  snprintf(str, size, format, 1, "2", 3);
  sprintf(str, format, 1, "2", 3);
  dprintf(1, format, 1, "3", "4");

  fprintf(stream, "%d %s %d", 1, "2", 3);
  printf("%d %s %d", 1, "2", 3);
  snprintf(str, size, "%d %s %d", 1, "2", 3);
  sprintf(str, "%d %s %d", 1, "2", 3);
  dprintf(1, "%d %s %s", 1, "3", "4");
}

