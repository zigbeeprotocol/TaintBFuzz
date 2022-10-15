/* run.config
   STDOPT: #" -warn-signed-downcast -print -machdep x86_32"
*/

struct STR { int num : 7; };

void foo(int a, long b) {
  struct STR s = { .num = 0 };
  s.num = b;
  s.num += a;
}
