/* run.config
   DONTRUN:
*/
/* run.config_qualif
   OPT: -wp-msg-key shell %{dep:@PTEST_DIR@/working_dir/swap.c} %{dep:@PTEST_DIR@/working_dir/swap1.h}
   OPT: -wp-msg-key shell -wp-rte %{dep:@PTEST_DIR@/working_dir/swap.c} %{dep:@PTEST_DIR@/working_dir/swap2.h}
PLUGIN: wp,rtegen,report
   OPT: -kernel-verbose 0 -wp-msg-key shell -wp-rte %{dep:@PTEST_DIR@/working_dir/swap.c} %{dep:@PTEST_DIR@/working_dir/swap2.h} -wp-verbose 0 -then -no-unicode -report
*/
void look_at_working_dir(void);
