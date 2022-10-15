/* run.config
   STDOPT: +"-machdep gcc_x86_32 -c11"
 */

__thread int a;
static __thread int b;
extern __thread int c;
_Thread_local int d;

_Thread_local int bad() { return 0; } // KO

_Thread_local int bad_also(void); // KO

int main() {
  _Thread_local int e = 1; // KO: e is neither extern nor static
  static _Thread_local int f = 0; // OK
  register _Thread_local int g = 1; // KO
  a = 0;
  b = 0;
  c = 0;
  d = 0;
  return 0;
}
