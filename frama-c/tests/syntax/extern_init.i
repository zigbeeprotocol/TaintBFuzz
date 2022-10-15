/* run.config
PLUGIN: eva,inout,scope
OPT: %{dep:@PTEST_DIR@/@PTEST_NAME@_1.i} %{dep:@PTEST_DIR@/@PTEST_NAME@_2.i} -eva @EVA_CONFIG@
OPT: %{dep:@PTEST_DIR@/@PTEST_NAME@_2.i} %{dep:@PTEST_DIR@/@PTEST_NAME@_1.i} -eva @EVA_CONFIG@
*/

extern int a[] ;

/*@ assigns a[3] \from \nothing; */
void g();
