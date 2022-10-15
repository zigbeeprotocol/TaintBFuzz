/* run.config
 DEPS: merge_union.h
   OPT: -cpp-extra-args="-I @PTEST_DIR@" %{dep:@PTEST_DIR@/@PTEST_NAME@_2.c} %{dep:@PTEST_DIR@/@PTEST_NAME@_3.c} -print
   OPT: -cpp-extra-args="-I @PTEST_DIR@" %{dep:@PTEST_DIR@/@PTEST_NAME@_2.c} %{dep:@PTEST_DIR@/@PTEST_NAME@_3.c} -print -kernel-warn-key="linker:drop-conflicting-unused=inactive"
*/
#include "merge_union.h"
int f(un* u);
