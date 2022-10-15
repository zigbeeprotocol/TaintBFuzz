/* run.config
 NOFRAMAC: testing frama-c-script, not frama-c itself
 COMMENT: the 'build' command cannot be tested because it requires 'glub'.
 DEPS: main2.c main3.c main.c
   EXECNOW: LOG list_files.res LOG list_files.err PTESTS_TESTING=1 %{bin:frama-c-script} list-files %{dep:@PTEST_DIR@/list_files.json} > @PTEST_RESULT@/list_files.res 2> @PTEST_RESULT@/list_files.err
 DEPS: for-find-fun2.c for-find-fun.c for-list-functions.c main2.c main3.c main.c make-wrapper2.c make-wrapper3.c make-wrapper.c
   EXECNOW: LOG find_fun1.res LOG find_fun1.err PTESTS_TESTING=1 %{bin:frama-c-script} find-fun main2 @PTEST_DIR@ > @PTEST_RESULT@/find_fun1.res 2> @PTEST_RESULT@/find_fun1.err
   EXECNOW: LOG find_fun2.res LOG find_fun2.err PTESTS_TESTING=1 %{bin:frama-c-script} find-fun main3 @PTEST_DIR@ > @PTEST_RESULT@/find_fun2.res 2> @PTEST_RESULT@/find_fun2.err
   EXECNOW: LOG find_fun3.res LOG find_fun3.err PTESTS_TESTING=1 %{bin:frama-c-script} find-fun false_positive @PTEST_DIR@ > @PTEST_RESULT@/find_fun3.res 2> @PTEST_RESULT@/find_fun3.err
 DEPS:
   EXECNOW: LOG list_functions.res LOG list_functions.err PTESTS_TESTING=1 %{bin:frama-c-script} list-functions %{dep:@PTEST_DIR@/for-find-fun2.c} %{dep:@PTEST_DIR@/for-list-functions.c} > @PTEST_RESULT@/list_functions.res 2> @PTEST_RESULT@/list_functions.err
   EXECNOW: LOG list_functions2.res LOG list_functions2.err LOG list_functions2.json PTESTS_TESTING=1 %{bin:frama-c-script} list-functions %{dep:@PTEST_DIR@/for-find-fun2.c} %{dep:@PTEST_DIR@/for-list-functions.c} -list-functions-declarations -list-functions-output @PTEST_RESULT@/list_functions2.json -list-functions-debug 1 > @PTEST_RESULT@/list_functions2.res 2> @PTEST_RESULT@/list_functions2.err
 */



void main() {

}
// NB: Dependency to ./share directory where are script files used by %{bin:frama-c-script} is implicit with `dune` testing.
