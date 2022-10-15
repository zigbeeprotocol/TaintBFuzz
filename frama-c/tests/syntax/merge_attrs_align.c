/*run.config
 EXIT: 1
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align1.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align2.c}"
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align1.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align3.c}"
 EXIT: 0
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align1.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align4.c}"
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align2.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align3.c}"
 EXIT: 1
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align2.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align4.c}"
  STDOPT: +"-machdep x86_64" +"%{dep:@PTEST_DIR@/merge_attrs_align3.c}" +"%{dep:@PTEST_DIR@/merge_attrs_align4.c}"
 */

// for testing with GCC/Clang
#ifndef __FRAMAC__
extern int f1();
extern int f2();
extern int f3();
extern int f4();

int main() {
  f1(); // 1
  f2(); // 2
  f3(); // 2
  f4(); // 1
  return 0;
}
#endif
