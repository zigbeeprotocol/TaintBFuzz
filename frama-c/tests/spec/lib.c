/* run.config
 DEPS: lib.h
   OPT: -cpp-extra-args="-Itests/spec" -cpp-extra-args="-include lib.h" -print
*/
/*@ ensures f((int)0) == (int)0; */
int main () { return 0; }
