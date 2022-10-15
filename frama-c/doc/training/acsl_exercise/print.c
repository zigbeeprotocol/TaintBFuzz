#include <stdio.h>

struct vector { unsigned int l; int d[99]; };

typedef struct vector *vector_ptr;

void print_vector(vector_ptr v)
{
  int i;
  printf("[ ");
  for(i=0; i<v->l; i++)
    {
      printf("%d; ",v->d[i]);
    }
  printf("]");
}

struct vector empty = { .l = 0 };

struct vector myvect = { .l = 3 , .d = { 1 , 2 , 3 } }; 

int main()
{
  printf("1. empty\n");
  print_vector (&empty);
  printf("\n2. myvect\n");
  print_vector (&myvect);
  return 0;
}

// non-zero if the vector's size is 0.
int empty(vector_ptr v);

// Returns the n'th element.
int get(vector_ptr v, unsigned int index);

// The assignment operator
void set(vector_ptr v, unsigned int index, int value);

// Returns the first element.
int front(vector_ptr v);

// Returns the last element.
int back(vector_ptr v);



