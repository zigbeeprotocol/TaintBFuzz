/* run.config
 LIBS: libSelect
 MODULE: @PTEST_NAME@
 DEPS: select_return.i
   OPT: @EVA_OPTIONS@ -deps -lib-entry -main g -slicing-level 3
*/

/* dummy source file in order to test minimal calls feature
 * on select_return.i  */

#include "select_return.i"
