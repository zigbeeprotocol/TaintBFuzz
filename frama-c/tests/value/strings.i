/* run.config*
  STDOPT: #"-eva-no-builtins-auto -eva-slevel-function strcmp:50"
*/

volatile int nondet;

char s1[]="hello\000 world";
char s2[]="hello";
char *s3="tutu";
char *s4="tutu";
char *s5, *s6;
char *s7="hello\x00 world";
char *s8="hello";

int u(void);

char cc = 'a';
char Q, R, S, T, U, V, W, X, Y, Z;

char *strcpy(char*dst, char*src) {
  char* ldst=dst;
  /*@ loop pragma UNROLL 20; */
  while (*ldst++ = *src++)
    ;
  return dst;
}

unsigned int strlen(char *s) {
  unsigned int l=0;
 /*@ loop pragma UNROLL 20; */
  while(*s++ != 0)
    l++;
  return l;
}

int string_reads() {
  char *p;
  p = &s1[3];
  if (u()) R=*(p-4);

  p = &s1[3];
  if (u()) S=*(p+12);

  if (u())
    p = &s1[5];
  else
    p = &s2[3];
  if (u()) T=*(p-4);

  {
    char a[10] = "Not ok";
    char b     [5];
    if (u()) strcpy(b,a);
  }

  s1[3]=cc;
  s1[6]=cc;
  return strlen(s1);
}

int string_writes() {
  char c=-1;
  if (nondet) s5 = s3; else s5 = &c;
  *(nondet ? s5 + 2 : &c) = 'T';
  R=c;
  *s5=' ';
  if (nondet) s6 = s3+1; else s6 = &c;
  *s6=cc;
  c=*s4;
  return c;
}


int string_comparison() {
  char *s;
  s = "toto";
  cc = *s;
  if (u())
    R = (s3 == s4);
  if (u())
    S = (s1 == s2);
  if (u())
    T = (s1 == s3);
  if (u())
    U = (s7 == s8);
  if (u())
    V = (s7 == s4);
  if (u())
    W = (s7 + 1 == s8 + 1);
  if (u())
    X = (s3 == s3);
  s5 =  (u()?s3:s8);
  if (u())
    Y = ((u()?s3:s8) == s5);
  s6 = (u()?(u()?s3:s8):s4);
  if (u())
    Z = (s5 == s6);
  if (u())
    Q = ("oh, hello"+4 == s7);
  return cc;
}

/* Currently, Eva does not support wide string comparisons: alarms are emitted
   on any comparison involving a wide string. Tests are minimal for now. */
int wide_string_comparison() {
  char* w1 = L"abcdef";
  char* w2 = L"def";
  char* w3 = L"abc";
  int res = 0;
  /* Must emit a comparison alarm. */
  if (w1 == w2)
    res = 1;
  /* Ideally, should not emit a comparison alarm. */
  if (w2 == w3)
    res = -1;
  return res;
}

int strcmp(const char *s1, const char *s2)
{
  if (s1 == s2)
    return (0);
  while (*s1 == *s2++)
    if (*s1++ == '\0')
      return (0);
  return (*(unsigned char *)s1 - *(unsigned char *)--s2);
}

//@ assigns p[0..s-1]; ensures \initialized(&p[0..s-1]);
void assigns(char *p, unsigned int s);

int long_chain() {
  char tc[30];
  char long_chain[] = "really really really long chain";
  assigns(&tc[0],30);
  int x = strcmp(long_chain, tc);
  return x;
}


void main() {
  string_reads ();
  string_writes ();
  string_comparison ();
  wide_string_comparison ();
  long_chain ();
}
