#include <locale.h>

int main() {
  struct lconv *lc = localeconv();
  return lc->decimal_point[0];
}
