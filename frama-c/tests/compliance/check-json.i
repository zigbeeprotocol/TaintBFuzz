/*run.config
 MACRO: SHARE @FRAMAC_SHARE@/compliance
 NOFRAMAC:
  EXECNOW: LOG json_@PTEST_NAME@_1.txt python3 -m json.tool < @SHARE@/c11_functions.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_1.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_2.txt python3 -m json.tool < @SHARE@/glibc_functions.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_2.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_3.txt python3 -m json.tool < @SHARE@/nonstandard_identifiers.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_3.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_4.txt python3 -m json.tool < @SHARE@/posix_identifiers.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_4.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_5.txt python3 -m json.tool < @SHARE@/compiler_builtins.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_5.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_6.txt python3 -m json.tool < @SHARE@/gcc_builtins.json | head -n 2 | tail -n 1 > @PTEST_RESULT@/json_@PTEST_NAME@_6.txt 2> @DEV_NULL@
  EXECNOW: LOG json_@PTEST_NAME@_7.txt python3 %{dep:@PTEST_DIR@/sanity-checks.py} @SHARE@ > @PTEST_RESULT@/json_@PTEST_NAME@_7.txt 2> @DEV_NULL@
*/
