/* run.config
   PLUGIN: @PTEST_PLUGIN@ inout,scope
   STDOPT: +"-metrics-eva-cover -then -main foo"
*/
void foo () {
  int i = 0;
  return;
}
/* foo is unreachable since j is always 0 */
int main() {
  int j = 0;
  if (!j) {
    return 1;
  }
  else {
    foo ();
    return 0;
  }
}
