/* run.config
   NOFRAMAC: testing frama-c-script, not frama-c itself
   EXECNOW: LOG @PTEST_NAME@.res LOG @PTEST_NAME@.err PTESTS_TESTING=1 %{bin:frama-c-script} estimate-difficulty @PTEST_FILE@ > @PTEST_NAME@.res 2> @PTEST_NAME@.err
*/

// these includes are not actually used by the compiler
// (this is a preprocessed file), but analyzed by the script
#include <sys/socket.h>
# include <complex.h>
  #	include <langinfo.h>
#include <sys/socket.h>

void g() {
  int g = 42;
}

void f() {
  if (v) f();
  else g();
}

int main() {
  va_arg(); // no warning: it is a macro, not a function
  setjmp(); // warning: problematic
  strlen(); // no warning
  ccosl(); // warning: neither code nor spec
  dprintf(); // no warning: neither code nor spec, but handled by Variadic
}
