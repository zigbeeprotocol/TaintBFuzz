/* run.config*
   STDOPT: +"-print -machdep gcc_x86_32"
*/

int sz_str,sz_typ,align_str,align_typ;

void main1()
{
  sz_str= sizeof("ONE");
  //@ assert sz_str == sizeof("ONE");
  align_str= __alignof("FOO");
  // assert align_str == __alignof("FOO");
  sz_typ= sizeof(char);
  //@ assert sz_typ == sizeof(char);
  align_typ= __alignof(char*);
  // assert align_typ == __alignof((char*));
  //@ assert sizeof("BLA") != sizeof("FOOBAR");
  return;
}

struct s {
  int t[10];
};

struct s s1;
volatile int i;

/* Test a not so intelligent bug of Logic_interp, that used to call
   the dependencies of the sizeof() construct present in the alarms. Since
   those have an array type, Value was unhappy. */
void main2() {
  struct s *p = (&s1 + (int)&s1) - (int)&s1; // creates a garbled mix
  p->t[sizeof(s1.t)-i] = 1;
  p->t[sizeof(s1.t)-i] = 2; 
}

/* Tests sizeof and alignof on void. Only valid in gcc machdeps. */
void sizeof_void () {
  void *p;
  int size_void = sizeof(void);
  int size_ptr = sizeof(p);
  int size_void_expr = sizeof(*p);
  int align_void = __alignof__(void);
  int align_ptr = __alignof__(p);
  int align_void_expr = __alignof__(*p);
}

void f(int sz) {}

void main(int *p, int *q, int j) {
  main1();
  main2();
  sizeof_void();
  f(sizeof(*p) * j); // must not crash with equality domain
}
