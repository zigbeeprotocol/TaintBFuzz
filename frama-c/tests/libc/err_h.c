/* run.config
   STDOPT:
*/
#include <err.h>
#include <stdarg.h>

volatile int nondet;

void vaw(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vwarn(fmt, ap);
  va_end(ap);
}

void vawx(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vwarnx(fmt, ap);
  va_end(ap);
}

void vae(int eval, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  verr(eval, fmt, ap);
  va_end(ap);
}

void vaex(int eval, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  verrx(eval, fmt, ap);
  va_end(ap);
}

int main() {
  int a = 1, *p = 2;
  warn(0);
  warn(0, a);
  warnx("%d", a);
  vaw("%s", "warn");
  vawx(0);
  if (nondet) {
    err(0, 0);
    //@ assert unreachable: \false;
  }
  if (nondet) {
    err(1, 0, a);
    //@ assert unreachable: \false;
  }
  if (nondet) {
    errx(2, "%d", a);
    //@ assert unreachable: \false;
  }
  if (nondet) {
    vae(0, 0);
    //@ assert unreachable: \false;
  }
  if (nondet) {
    vaex(-1, "nogood %d", a);
    //@ assert unreachable: \false;
  }
  return 0;
}
