/* run.config*
   FILTER: sed "s:/[^ ]*[/]cpp-command\.[^ ]*\.i:TMPDIR/FILE.i:g; s:$PWD/::g; s:$(realpath @FRAMAC_SHARE@)/:FRAMAC_SHARE/:g; s:@PTEST_MAKE_DIR@/result@PTEST_CONFIG@/::g; s: -m32::"
   OPT: -machdep x86_32 -cpp-frama-c-compliant -cpp-command "echo [\$(basename '%1') \$(basename '%1') \$(basename '%i') \$(basename '%input')] ['%2' '%2' '%o' '%output'] ['%args']"
   OPT: -machdep x86_32 -cpp-frama-c-compliant -cpp-command "echo %%1 = \$(basename '%1') %%2 = '%2' %%args = '%args'"
   OPT: -machdep x86_32 -cpp-frama-c-compliant -cpp-command "printf \"%s\n\" \"using \\% has no effect : \$(basename \"\%input\")\""
   OPT: -machdep x86_32 -cpp-frama-c-compliant -cpp-command "echo %var is not an interpreted placeholder"
   OPT: -machdep x86_32 -print-cpp-commands
   OPT: -cpp-extra-args-per-file=@PTEST_FILE@:"-DPF=\\\"cp%02d_%.3f\\\"" -cpp-extra-args="-DPF2=\\\"cp%02d_%.3f\\\"" -no-autoload-plugins @PTEST_FILE@ -print
   OPT: -cpp-extra-args-per-file=@PTEST_FILE@:"file_extra" -cpp-extra-args="global_extra" -cpp-command "echo 'extra_args: %args'" -no-autoload-plugins @PTEST_FILE@ -print
   */
#include <stdio.h>
void printer(int i, float f) {
  printf(PF, i, f);
}

int main() {
  printer(1, 1.0);
}
