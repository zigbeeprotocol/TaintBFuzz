/* run.config
   STDOPT: #"-c11"
   EXIT: 1
   STDOPT: #"-c11 -cpp-extra-args=-DFAIL"
*/

_Static_assert(1, "string");

#include <assert.h>

#ifdef FAIL
static_assert(0, "fail");
#endif

_Static_assert(2); // without message string; this is not C11-compliant, but
                   // a C++17 extension. GCC/Clang allow it.

// _Static_assert can also appear inside struct declarations
struct st { _Static_assert (sizeof(char) == 1, "inside struct"); int a; };

int main() {
  static_assert(sizeof(int) > sizeof(char), "int must be greater than char");

#ifdef FAIL
  int a = 42;
  static_assert(a == 42, "non-static condition");
#endif

  int ret = 42;

  static_assert(3); // between statements

  return ret;
}

#ifdef FAIL
static_assert(0); // fail without message string
struct st2 { _Static_assert (sizeof(char) > 1, "failure inside struct"); int a; };
#endif
