/* run.config*
 COMMENT: with dune, the LIBS directive must be replaced by a MODULE directive (see also ./test_config file)

 LIBS: global_decl_loc
   OPT: %{dep:@PTEST_DIR@/global_decl_loc.i}
*/
extern int g;

int main(void) {
  int a = g;
  return a;
}
