/* run.config*
MODULE: @PTEST_NAME@
STDOPT:
*/
void __FC_assert(int c);
enum a {HA};
enum a b;
int main() {
  __FC_assert(!b);
}
