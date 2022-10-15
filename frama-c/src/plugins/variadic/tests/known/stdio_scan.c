#include <stdio.h>

int main(){
  FILE *stream;
  char *format;
  char *str;
  int i, j;
  char *s;

  fscanf(stream, format, &i, s, &j);
  scanf(format, &i, s, &j);
  sscanf(str, format, &i, s, &j);

  fscanf(stream, "%d %s %d", &i, s, &j);
  scanf("%d %s %d", &i, s, &j);
  sscanf(str, "%d %s %d", &i, s, &j);
}
