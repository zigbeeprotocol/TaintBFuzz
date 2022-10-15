/* run.config
 NOFRAMAC: testing frama-c-script, not frama-c itself

 DEPS: @PTEST_DEPS@ @PTEST_DIR@/for-find-fun.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/for-find-fun2.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/for-list-functions.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/list_functions.i
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/main.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/main2.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/main3.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/make-wrapper.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/make-wrapper2.c
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/make-wrapper3.c

 DEPS: @PTEST_DEPS@ @PTEST_DIR@/build-callgraph.i
 DEPS: @PTEST_DEPS@ @PTEST_DIR@/recursions.i

   EXECNOW: LOG heuristic_list_functions.res LOG heuristic_list_functions.err PTESTS_TESTING=1 %{bin:frama-c-script} heuristic-list-functions true true @PTEST_DEPS@ > @PTEST_RESULT@/heuristic_list_functions.res 2> @PTEST_RESULT@/heuristic_list_functions.err
 */
