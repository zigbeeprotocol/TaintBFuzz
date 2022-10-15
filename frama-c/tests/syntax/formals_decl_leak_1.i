/* run.config
DONTRUN: main test is located in @PTEST_DIR@/formals_decl_leak.i
*/

void f(int y);

void h () { f(4); }
