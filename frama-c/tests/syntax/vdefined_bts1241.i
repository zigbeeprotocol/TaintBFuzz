/* run.config
STDOPT: +"%{dep:@PTEST_DIR@/vdefined_bts1241_1.i}"
 */

int f();

int g() { return 0; }

int f() { return 1; }

int g();

int h();

int h1() { return h(); }
