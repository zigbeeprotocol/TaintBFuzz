/* run.config
   OPT: -print %{dep:@PTEST_DIR@/multiple_decl_def_2.c}
*/

/* see bug #43 && #128 */

/*@ requires x >= 0; */
extern int f(int x);

/*@ requires x >= 0; */
extern int g(int x);

int main () { g(0); return f(0); }
