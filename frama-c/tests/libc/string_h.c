#include <string.h>

void test_strcmp(void)
{
  int res = strcmp("hello", "world");
  //@ assert res == 0;
}

void test_strcat(void)
{
  char string[10];
  string[0] = 0;
  strcat(string, "hello");
  char string2[10];
  string2[0] = 0;
  strcat(string2, string);
}

volatile int nondet;
void test_strstr(void)
{
  char *s = nondet ? "aba" : "bab";
  char *needle = nondet ? "a" : "b";
  char *res = strstr(s, needle);
  //@ assert res != 0;
}

void test_strncat(void)
{
  char data[100];
  data[0] = '\0';
  char source[100];
  //@ slevel 99;
  for (int i = 0; i < 99; i++) source[i] = 'Z';
  source[99] = '\0';
  strncat(data, source, 100);
}

struct s {
  char s1[30];
  char s2[30];
};

// this test crashes GCC (tested with v7.1.1) due to the non-respect of
// non-aliasing in strcpy
void crashes_gcc() {
  struct s s;
  char *ss = "ABCDEFGHIJKLMNOPQRSTUVWXYZ012";
  //@ slevel 30;
  for (int i = 0; i < 30; i++) s.s1[i] = ss[i];
  char *dest = s.s1+29;
  char *src = s.s1;
  strcpy(dest, src); // must produce at least a warning
}

void test_strtok() {
  if (nondet) {
    strtok(NULL, " "); // must fail
    //@ assert unreachable: \false;
  }
  char buf[2] = {0};
  char *a = strtok(buf, " ");
  //@ assert a == \null || \subset(a, buf+(0..));
  char *b = strtok(NULL, " ");
  //@ assert b == \null || \subset(b, buf+(0..));
  char buf2[4] = "abc";
  char *p = strtok(buf2, "b");
  //@ assert p == \null || \subset(p, buf2+(0..));
  char *q = strtok(NULL, "c");
  //@ assert q == \null || \subset(p, buf2+(0..));
  // test with non-writable string, but delimiter not found
  char *r = strtok((char*)"constant!", "NONE_TO_BE_FOUND");
  //@ assert r == \null;
  if (nondet) {
    strtok((char*)"constant!", "!");
    //@ assert unreachable_if_precise: \false;
  }
}

void test_strtok_r() {
  if (nondet) {
    strtok_r(NULL, " ", NULL); // must fail
    //@ assert unreachable: \false;
  }
  char *saveptr;
  char buf[2] = {0};
  char *a = strtok_r(buf, " ", &saveptr);
  if (nondet) {
    strtok_r(buf, " ", NULL); // must fail
    //@ assert unreachable: \false;
  }
  //@ assert a == \null || \subset(a, buf+(0..));
  char *b = strtok_r(NULL, " ", &saveptr);
  Frama_C_show_each_saveptr(saveptr);
  //@ assert b == \null || \subset(b, buf+(0..));
  char buf2[4] = "abc";
  char *p = strtok_r(buf2, "b", &saveptr);
  //@ assert p == \null || \subset(p, buf2+(0..));
  char *q = strtok_r(NULL, "c", &saveptr);
  //@ assert q == \null || \subset(p, buf2+(0..));
  // test with non-writable string, but delimiter not found
  char *r = strtok_r((char*)"constant!", "NONE_TO_BE_FOUND", &saveptr);
  //@ assert r == \null;
  if (nondet) {
    strtok_r((char*)"constant!", "!", &saveptr);
    //@ assert unreachable_if_precise: \false;
  }
}

void test_strncpy() {
  char src[] = { 'a', 'b', 'c' };
  char dst[3];
  strncpy(dst,src,3);
  char src2[3];
  src2[0] = 'a';
  src2[1] = 'b';
  if (nondet) {
    strncpy(dst,src2,3);
    //@ assert unreachable: \false;
  }
}

void test_strlcpy() {
  char buf[16];
  char buf2[32];
  size_t r1 = strlcpy(buf, "longer than buffer", 16);
  size_t r2 = strlcpy(buf2, "short", 16);
  size_t r3 = strlcat(buf2, buf, 32);
  char src[] = { 'a', 'b', 'c' };
  char dst[3];
  if (nondet) {
    strlcpy(dst,src,3);
    //@ assert unreachable: \false;
  }
}

int main(int argc, char **argv)
{
  test_strcmp();
  test_strcat();
  test_strstr();
  test_strncat();
  if (!nondet) crashes_gcc();
  test_strtok();
  test_strtok_r();
  char *a = strdup("bla"); // unsound; specification currently unsupported
  char *b = strndup("bla", 2); // unsound; specification currently unsupported
  char *strsig = strsignal(1);
  //@ assert valid_read_string(strsig);
  test_strncpy();
  test_strlcpy();
  char *c = "haystack";
  char d = nondet ? 'y' : 'k';
  char *chr1 = strchr(c, d);
  char *nul1 = strchrnul(c, d);
  d = nondet ? 'a' : 'n';
  char *chr2 = strchr(c, d);
  char *nul2 = strchrnul(c, d);
  char pdest[10];
  char *pend = mempcpy(pdest, "gnu-only function", 9);
  //@ assert imprecise: pend == pdest + 9 && *pend == '\0';
  return 0;
}
