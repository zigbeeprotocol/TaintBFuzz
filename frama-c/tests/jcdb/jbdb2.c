/* run.config
OPT: -json-compilation-database %{dep:@PTEST_DIR@/build_commands.json} -print
*/

int f1 () {
  return RETCODE; // defined in build_commands.json
}
