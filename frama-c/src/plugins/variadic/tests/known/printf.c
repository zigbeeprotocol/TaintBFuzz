#include <stdlib.h>
#include <inttypes.h>
#include <wchar.h>
#include <stddef.h>
#include <stdio.h>

#include <stdio.c>


int main()
{
  char *string = "Hello world !\n";
  wchar_t *wstring = L"Hello world !\n";
  char c = '4';
  signed char hh;
  unsigned char uhh = 42;
  short h;
  unsigned short uh = 42;
  int i;
  unsigned int ui = 42;
  long int l;
  unsigned long int ul = 42;
  long long int ll;
  unsigned long long int ull = 42;
  intmax_t j;
  uintmax_t uj = 42;
  size_t z;
  ptrdiff_t t;
  double f = 42.0f;
  long double L = 42.0l;
  uint64_t u64 = 42ul;
  int8_t i8 = 42;
  uint_least64_t uleast64 = 42u;
  int_fast32_t ifast32 = 42;
  //wint_t win = '2';

  printf("Hello world !\n");
  printf("%s%n", string, &i);
  printf("%ls", wstring);

  printf("%d %hhn", i, &hh);
  printf("%hhi %hn", hh, &h);
  printf("%hd %ln", h, &l);
  printf("%li %lln", l, &ll);
  printf("%lld %jn", ll, &j);
  printf("%jd %zn", j, &z);
  printf("%zd %tn", z, &t);
  printf("%td\n", t);

  printf("%u ", ui);
  printf("%hho ", uhh);
  printf("%hx ", uh);
  printf("%lX ", ul);
  printf("%llu ", ull);
  printf("%jo ", uj);
  printf("%zx %tX\n", z, t);

  printf("%" PRIu64, u64);
  printf("%" PRIi8, i8);
  printf("%" PRIxLEAST64, uleast64);
  printf("%" PRIdFAST32, ifast32);

  printf("%f %Le\n", f, L);

  printf("%c\n", c);
  //printf("%c%lc\n", c, win);

  printf("%p ", string);
  printf("%d %*.*u\n", 1, -(-1), 2, ui);

  printf("Hello %- 0+#20.10lx %% %s world %d !", ui, string, 42);

  char hashes[4] = "####"; // no terminator
  printf("%.*s", 4, hashes); // ok
  printf("%.4s", hashes); // ok
}
