/* run.config
 PLUGIN: @PTEST_PLUGIN@ inout
 EXECNOW: LOG @PTEST_NAME@_metrics.res LOG @PTEST_NAME@_metrics.err @frama-c@ @PTEST_FILE@ -metrics -metrics-libc -then -metrics-no-libc | %{dep:@PTEST_SUITE_DIR@/../libc/check_some_metrics.sh} "> 5" "> 100" "= 0" "> 10" "= 2"  "= 6" "= 0" "= 0" "= 0" "= 4" >@PTEST_NAME@_metrics.res 2>@PTEST_NAME@_metrics.err
   STDOPT: #"-metrics-eva-cover"
   LOG: libc.json
   STDOPT: #"-metrics-libc -metrics-output @PTEST_RESULT@/libc.json"
*/
#include <ctype.h>
#include <stdio.h> // defines external variables
#include <getopt.h>

// getopt will have the fc_stdlib attribute, but foo and bar won't;
// ensure they are not skipped during syntactic search

int foo() { return 42; }

int bar() { return 42; }

int f() { // never called
  return getchar();
}

int g() { // called via fp
  return isalpha(42);
}

int h() { return 0; }

int (*fp)() = g;

int getopt(int argc, char * const argv[],
           const char *optstring) {
  return foo() + bar();
}

int main() {
  fp();
  getopt(0, 0, 0);
  h();
  return isblank(0);
}
