/* run.config
 DEPS: compile_commands.json
 COMMENT: parsing option are defined in the default json file "compile_commands.json"
   OPT: -json-compilation-database @PTEST_DIR@ -print
 DEPS:
   OPT: %{dep:@PTEST_DIR@/jcdb2.c} -json-compilation-database %{dep:@PTEST_DIR@/with_arguments.json} -print
 MODULE: @PTEST_NAME@
   OPT: -json-compilation-database %{dep:@PTEST_DIR@/with_arguments.json}
 MODULE:
 DEPS: file_without_main.c
   EXECNOW: LOG list_files.res LOG list_files.err %{bin:frama-c-script} list-files %{dep:@PTEST_DIR@/compile_commands_working.json} > @PTEST_RESULT@/list_files.res 2> @PTEST_RESULT@/list_files.err
*/

#include <stdio.h>

#ifdef TOUNDEF
#error TOUNDEF must be undefined by the compilation database
#endif

int main () {
  char *s = DOUBLE_SINGLE("a ");
  #ifndef __FRAMAC__
  printf("%s\n", s); // for GCC debugging
  #endif
  return MACRO_FOR_INCR(TEST); }
