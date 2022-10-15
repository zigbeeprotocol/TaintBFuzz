/* run.config
 COMMENT: test related to a bugfix in the management of relative sub-directories:
 DEPS: logic-pp-include/compile_commands.json
   OPT: -json-compilation-database @PTEST_DIR@/logic-pp-include %{dep:@PTEST_DIR@/logic-pp-include/no-stdio.c} -print
*/
