/* run.config
   COMMENT: test of a local initializer which contains an annotation
   STDOPT: #"@MACHDEP@ -lib-entry -eva -then -no-lib-entry"
*/

int X = 0;
int *p = &X;

int f(void) {
  int x = *p; // Eva's alarm in -lib-entry on this local initializer
  return x;
}

int main(void) {
  f();
  return 0;
}
