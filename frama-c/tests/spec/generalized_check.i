/* run.config
PLUGIN: eva,inout,scope
    OPT: -eva -eva-use-spec f
PLUGIN:
    OPT: -print
*/
/*@ check lemma easy_proof: \false; */ // should not be put in any environment
/*@ check requires f_valid_x: \valid(x);
    assigns *x;
    check ensures f_init_x: *x == 0;
*/
void f(int* x) {
  /*@ check f_valid_ko: \valid(x); */
  *x = 0;
}

void loop(void);

int main() {
  int a = 4;
  volatile int c;
  int* p = (void*)0;
  if (c) p = &a;
  f(p);
  /*@ check main_valid_ko: \valid(p); */
  /*@ check main_p_content_ko: *p == 0; */
  loop();
}

void loop () {
  int j = 0;
  /*@ check loop invariant false_but_preserved: j == 10;
      loop assigns i;
   */
  for (int i = 0; i< 10; i++);
  /*@ check implied_by_false_invariant: j == 10; */
 l: /*@ check invariant \true; */ ;
  if (j >= 10) goto l1;
  j++;
  goto l;
 l1 : ;
}
