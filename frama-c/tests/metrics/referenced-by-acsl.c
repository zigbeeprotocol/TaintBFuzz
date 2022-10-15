/* run.config
   PLUGIN: @PTEST_PLUGIN@ inout
   STDOPT: +"-metrics-eva-cover"
**/

void f() {}

/*@ requires \valid_function(&f); */
int main () {}
