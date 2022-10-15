/* run.config
STDOPT: +"-c11 -warn-invalid-pointer -print"
*/

struct S { void (*f)(void); } s;

struct S1 { void(*f)(void); } s1;

void (*p)(void);

void f(void) {
  if (p) return; // should not warn
  if (p+2) return; // should warn
  if (s.f) return; //should not warn
  if (s.f+2) return; // should warn
  return;
}

struct { union { void(*g)(void); unsigned int x; }; } s2;

struct { void (*tab[12])(void); } s3;

void write_something(void *x);

void h() {
  write_something(&s1.f);
  write_something(&s3.tab[4]);
}

//all the pointers below can have their value set to an invalid pointer without
// generating a warning at write site, hence a warning should be generated
// at read access.
void g(void) {
  if (s2.g) return;
  if (s1.f) return;
  if (s3.tab[4]) return;
}
