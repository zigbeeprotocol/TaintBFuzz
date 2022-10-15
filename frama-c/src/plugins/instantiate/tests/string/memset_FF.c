#include <string.h>

struct X {
  int x ;
  int y ;
} ;

typedef int named ;

void chars(char dest[10]){
  char* res = memset(dest, 0xFF, 10);
  memset(res, 0xFF, 10);
}

void uchars(unsigned char dest[10]){
  unsigned char* res = memset(dest, 0xFF, 10);
  memset(res, 0xFF, 10);
}

void nested_chars(char dest[10][10]){
  char (*res) [10] = memset(dest, 0xFF, 100);
  memset(res, 0xFF, 100);
}

void integer(int dest[10]){
  int * res = memset(dest, 0xFF, 10 * sizeof(int));
  memset(res, 0xFF, 10 * sizeof(int));
}

enum E { A, B, C } ;
void with_enum(enum E dest[10]){
  enum E * res = memset(dest, 0xFF, 10 * sizeof(enum E));
  memset(res, 0xFF, 10 * sizeof(enum E));
}

void unsigned_integer(unsigned dest[10]){
  unsigned * res = memset(dest, 0xFF, 10 * sizeof(unsigned));
  memset(res, 0xFF, 10 * sizeof(unsigned));
}

void long_integer(long int dest[10]){
  long int * res = memset(dest, 0xFF, 10 * sizeof(long int));
  memset(res, 0xFF, 10 * sizeof(long int));
}

void unsigned_long_integer(unsigned long int dest[10]){
  unsigned long int * res = memset(dest, 0xFF, 10 * sizeof(unsigned long int));
  memset(res, 0xFF, 10 * sizeof(unsigned long int));
}

void long_long_integer(long long int dest[10]){
  long long int * res = memset(dest, 0xFF, 10 * sizeof(long long int));
  memset(res, 0xFF, 10 * sizeof(long long int));
}

void unsigned_long_long_integer(unsigned long long int dest[10]){
  unsigned long long int * res =
    memset(dest, 0xFF, 10 * sizeof(unsigned long long int));
  memset(res, 0xFF, 10 * sizeof(unsigned long long int));
}

void floats(float dest[10]){
  float * res = memset(dest, 0xFF, 10 * sizeof(float));
  memset(res, 0xFF, 10 * sizeof(float));
}

void with_named(named dest[10]){
  named * res = memset(dest, 0xFF, 10 * sizeof(named));
  memset(res, 0xFF, 10 * sizeof(named));
}

void structure(struct X dest[10]){
  struct X * res = memset(dest, 0xFF, 10 * sizeof(struct X));
  memset(res, 0xFF, 10 * sizeof(struct X));
}

void pointers(int* dest[10]){
  int ** res = memset(dest, 0xFF, 10 * sizeof(int*));
  memset(res, 0xFF, 10 * sizeof(int*));
}

void nested(int (*dest)[10], int n){
  int (*res) [10] = memset(dest, 0xFF, n * sizeof(int[10]));
  memset(res, 0xFF, n * sizeof(int[10]));
}

void with_void(void* dest){
  void* res = memset(dest, 0xFF, 10);
  memset(res, 0xFF, 10);
}

void with_null_or_int(void){
  memset(NULL, 0xFF, 10);
  memset((int*) 42, 0xFF, 10);
}
