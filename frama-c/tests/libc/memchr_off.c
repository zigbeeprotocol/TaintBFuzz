#include <string.h>
#include <wchar.h>

void main() {
  char *s = "abc";
  //@ check valid: memchr_off(s, 'a', 3) == 0;
  //@ check valid: memchr_off(s, 'b', 3) == 1;
  //@ check not_found: memchr_off(s, 'b', 1) == 0;
  //@ check valid: memchr_off(s, 'b', 2) == 1;
  //@ check not_found: memchr_off(s, 'd', 2) == 1;
  //@ check not_found: memchr_off(s, 'd', 5) == 4;
  //@ check valid: memchr_off(s+1, 'b', 5) == 0;
  //@ check zero_length: memchr_off(s, 'a', 0) == -1;
  char *t = s+1;
  //@ check valid: memchr_off(&t[-1], 'b', 3) == 1;
  //@ check not_found: memchr_off(&s[-1], 'a', 3) == 2;

  wchar_t *ws = L"abc";
  //@ check valid: wmemchr_off(ws, (wchar_t)L'a', 3) == 0;
  //@ check valid: wmemchr_off(ws, (wchar_t)L'b', 3) == 1;
}
