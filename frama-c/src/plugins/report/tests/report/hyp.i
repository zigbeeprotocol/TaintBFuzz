/* run.config
  SCRIPT: one_hyp
   OPT:
  SCRIPT: several_hyps
   OPT:
*/
void f(void);
void f2(void);
void g() {
  /*@ assert \true; */
}

void h() {
  /*@ assert \false; */
}

void i() {
  /*@ assert 1 == 2; */
}

void j() {
  /*@ assert 2 == 3; */
}

void main() {
  /*@ assert 0 == 1; */
  f();
  f2();
  g();
  h();
  i();
  j();
}
