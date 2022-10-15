/* run.config
 COMMENT: Test `strcmp` and `strncmp` E-ACSL built-ins
 DEPS: @PTEST_DEPS@ utils/signalled.h
   STDOPT:
 COMMENT: This part is blank on purpose (test stability + Dune)




*/

#include "utils/signalled.h"
#include <stdlib.h>
#include <string.h>

static inline void fail_ncomp(int cond, char *fmt, int l, int r) {
  if (cond) {
    fprintf(stderr, fmt, l, r);
    abort();
  }
}

#define EQ(l, r)  fail_ncomp(l != r, "comparison failure: %d == %d\n", l, r)
#define NEQ(l, r) fail_ncomp(l == r, "comparison failure: %d != %d\n", l, r)

int main(int argc, const char **argv) {
  const char *cl = "abc", *cr = "abc";

  char al[4] = "abc", ar[4] = "abc";

  char *dl = strdup("abc"), *dr = strdup("abc");

  int res;
  /* strcmp {{{ */

  OK(EQ(strcmp(cl, cr), 0)); // valid comparison of constants [ok]
  OK(EQ(strcmp(al, ar), 0)); // valid comparison of stack strings [ok]
  OK(EQ(strcmp(dl, dr), 0)); // valid comparison of heap strings [ok]

  al[3] = 'a';
  ABRT(EQ(strcmp(al, ar), 0)); // unterminated in left stack [ok]
  ar[3] = 'a';
  al[3] = 0;
  ABRT(EQ(strcmp(al, ar), 0)); // unterminated in right stack [ok]
  dl[3] = 'a';
  ABRT(EQ(strcmp(dl, dr), 0)); // unterminated in left heap [ok]
  dr[3] = 'a';
  dl[3] = 0;
  ABRT(EQ(strcmp(dl, dr), 0)); // unterminated in right heap [ok]

  ABRT(EQ(strcmp(dl, NULL), 0)); // NULL in left  [ok]
  ABRT(EQ(strcmp(NULL, dr), 0)); // NULL in right [ok]

  free(dl);
  free(dr);

  ABRT(EQ(strcmp(dl, ar), 0)); // dangling in left  [ok]
  ABRT(EQ(strcmp(al, dr), 0)); // dangling in right [ok]

  /* }}} */

  /* strncmp {{{ */

  dl = strdup("abc"), dr = strdup("abc");

  char nal[4] = "abc", nar[4] = "abc";

  OK(EQ(strncmp(cl, cr, 3), 0));   // valid comparison of constants [ok]
  OK(EQ(strncmp(nal, nar, 3), 0)); // valid comparison of stack strings [ok]
  OK(EQ(strncmp(dl, dr, 3), 0));   // valid comparison of heap strings [ok]
  // Still ok because there is a terminator
  OK(EQ(strncmp(nal, nar, 6), 0)); // valid comparison of stack strings [ok]
  OK(EQ(strncmp(dl, dr, 6), 0));   // valid comparison of heap strings [ok]

  nal[3] = 'd';
  // no terminator but within allocated length [ok]
  OK(NEQ(strncmp(nal, nar, 4), 0));
  nar[3] = 'd';
  nal[3] = 0;
  OK(NEQ(strncmp(nal, nar, 4), 0));
  dl[3] = 'd';
  OK(NEQ(strncmp(dl, dr, 4), 0));
  dr[3] = 'd';
  dl[3] = 0;
  OK(NEQ(strncmp(dl, dr, 4), 0));

  // no terminator but outside allocated length [abort]
  ABRT(res = strncmp(nal, nar, 5));
  nal[3] = 'd';
  nar[3] = 0;
  ABRT(res = strncmp(al, ar, 5));
  ABRT(res = strncmp(dl, dr, 5));
  dl[3] = 'd';
  dr[3] = 0;
  ABRT(res = strncmp(dl, dr, 5));

  free(dl);
  free(dr);

  /* }}} */
  return 0;
}
