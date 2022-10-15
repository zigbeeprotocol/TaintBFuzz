/* run.config
 DEPS: anon_enum_libc.h
   OPT: -cpp-extra-args="-I @PTEST_DIR@" -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.c -print -then -ocode="" @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.c -print
*/
struct { int x; float y; } s1;
enum { BLA=4, BLI=12 };

#include "anon_enum_libc.h"

int f() { return BLA + s1.x; }

int g() { return FOO + s2.t; }
