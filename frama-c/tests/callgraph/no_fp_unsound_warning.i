/* run.config
PLUGIN: @PTEST_PLUGIN@ eva,scope,inout
   COMMENT: Test that callgraph users are warned about -cg-no-function-pointers
   OPT: -cg-function-pointers -out
   OPT: -cg-no-function-pointers -out
*/
void main() {
}
