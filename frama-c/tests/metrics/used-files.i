/* run.config
   MACRO: SOURCES %{dep:@PTEST_DIR@/@PTEST_NAME@1.i} %{dep:@PTEST_DIR@/@PTEST_NAME@2.i} %{dep:@PTEST_DIR@/@PTEST_NAME@3.i} %{dep:@PTEST_DIR@/@PTEST_NAME@4.i} %{dep:@PTEST_DIR@/@PTEST_NAME@5.i} %{dep:@PTEST_DIR@/@PTEST_NAME@6.i} %{dep:@PTEST_DIR@/@PTEST_NAME@7.i} %{dep:@PTEST_DIR@/@PTEST_NAME@8.i} %{dep:@PTEST_DIR@/@PTEST_NAME@9.c} %{dep:@PTEST_DIR@/@PTEST_NAME@1.h} %{dep:@PTEST_DIR@/@PTEST_NAME@2.h}
   DEPS: @PTEST_DIR@/@PTEST_NAME@10.c
   OPT: -metrics-used-files @SOURCES@
   OPT: -metrics-used-files -main g @SOURCES@
*/

int h(void);

extern int glob;

void indirect(void);

void indirect_unused(void);

int k(void);

int main() {
  void (*fp)() = indirect;
  fp();
  return h() + glob + k();
}
