/* run.config
   COMMENT: While unsupported, struct comparison should fail gracefully instead
   COMMENT: of crashing Frama-C (issue frama-c/e-acsl#139).
 */
struct X {
  int i;
};

/*@ ensures *\old(item) == \old(*item); */
void f(struct X *item) {}

int main() {
  struct X x = {.i = 1};
  f(&x);
  return 0;
}
