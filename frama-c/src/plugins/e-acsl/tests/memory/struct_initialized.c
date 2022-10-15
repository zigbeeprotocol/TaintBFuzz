#include <stdint.h>
#include <stdlib.h>

typedef struct {
  int32_t a;
  int32_t b;
} int32_pair_t;

int main() {
  // Static alloc
  {
    int32_pair_t static_pair;
    //@ assert !\initialized(&static_pair.a);
    //@ assert !\initialized(&static_pair.b);
    static_pair.a = 1;
    //@ assert \initialized(&static_pair.a);
    //@ assert !\initialized(&static_pair.b);
    static_pair.b = 2;
    //@ assert \initialized(&static_pair.a);
    //@ assert \initialized(&static_pair.b);
  }

  // Dynamic alloc
  {
    int32_pair_t *heap_pair = malloc(sizeof(int32_pair_t));
    //@ assert !\initialized(&heap_pair->a);
    //@ assert !\initialized(&heap_pair->b);
    heap_pair->a = 3;
    //@ assert \initialized(&heap_pair->a);
    //@ assert !\initialized(&heap_pair->b);
    heap_pair->b = 4;
    //@ assert \initialized(&heap_pair->a);
    //@ assert \initialized(&heap_pair->b);
  }
}
