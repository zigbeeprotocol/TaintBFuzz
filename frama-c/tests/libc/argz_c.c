/*run.config
  STDOPT: #"-eva-precision 6 -eva-alloc-builtin fresh"
*/

#ifdef __FRAMAC__
# include "argz.c"
# include "string.c"
#else
# include <argz.h>
# include <string.h>
#endif
#include <assert.h>
#include <stdlib.h>

int main() {
  error_t res;
  char *argv[] = {"this", "is", "argz", 0};
  char *argz;
  size_t len;
  res = argz_create(argv, &argz, &len);
  if (res) exit(1);
  //@ assert len == strlen("this") + 1 + strlen("is") + 1 + strlen("argz") + 1;
  free(argz);

  res = argz_create_sep("a b  cd", ' ', &argz, &len);
  if (res) exit(1);
  assert(len == 7);
  res = argz_count(argz, len);
  assert(res == 3);
  res = argz_add(&argz, &len, "ef");
  if (res) exit(1);
  assert(len == 10);
  res = argz_add_sep(&argz, &len, "gh:ij", ':');
  if (res) exit(1);
  assert(len == 16);
  res = argz_count(argz, len);
  assert (res == 6);
  res = argz_append(&argz, &len, "k", 2);
  if (res) exit(1);
  assert(len == 18);
  res = argz_add(&argz, &len, "ef");
  if (res) exit(1);
  assert(len == 21);
  unsigned replace_count = 1;
  res = argz_replace(&argz, &len, "ef", "bla", &replace_count);
  if (res) exit(1);
  assert(replace_count == 3);
  assert(len == 23);
  char *p = argz_next(argz, len, NULL);
  assert(*p == 'a');
  while (*p != 'b') {
    p = argz_next(argz, len, p);
  }
  argz_delete(&argz, &len, p);
  assert(len == 21);
  p = argz_next(argz, len, NULL);
  while (*p != 'b') {
    p = argz_next(argz, len, p);
  }
  assert(*(p+1) == 'l'); // found 'b' in 'bla'
  argz_delete(&argz, &len, p);
  assert(len == 17);
  p = argz_next(argz, len, NULL);
  res = argz_insert(&argz, &len, p, "mno");
  if (res) exit(1);
  assert(len == 21);
  res = argz_insert(&argz, &len, NULL, "zz");
  if (res) exit(1);
  assert(len == 24);

  free(argz);
  return 0;
}
