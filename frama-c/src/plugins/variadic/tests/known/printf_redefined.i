typedef long unsigned int size_t;

extern int printf(__const char *__restrict __format, ...);

void main() {
  long x = 0;
  printf("%zd\n", x);
}

