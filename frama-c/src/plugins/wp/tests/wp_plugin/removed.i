/* run.config_qualif
PLUGIN: @PTEST_PLUGIN@,rtegen,eva,scope,inout
   OPT: -no-wp -eva -eva-msg-key=-summary -then -wp -then -no-eva -warn-unsigned-overflow -wp
 */
/* run.config
   DONTRUN:
*/

int main(int i) { return 1+i; }
