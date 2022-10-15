// Qualified Type-Array Size

#define N 0xFFu
#define P 128L
#define Q 0x8A
#define R 'r'

int a[N];
int b[P];
int c[Q];
int d[R];

typedef int Ta[N];
typedef int Tb[P];
typedef int Tc[Q];
typedef int Td[R];

int sa = sizeof(int[N]);
int sb = sizeof(int[P]);
int sc = sizeof(int[Q]);
int sd = sizeof(int[R]);

/*@
  requires \valid(n + (0 .. sizeof(int[N])));
  requires \valid(p + (0 .. sizeof(int[P])));
  requires \valid(q + (0 .. sizeof(int[Q])));
  requires \valid(r + (0 .. sizeof(int[R])));
  assigns \nothing;
 */
void f(int *n, int *p, int *q, int* r);
