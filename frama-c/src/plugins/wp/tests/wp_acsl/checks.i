/* run.config
PLUGIN: @PTEST_PLUGIN@,rtegen,scope,eva,report,inout
   OPT: -then -eva -then -report
PLUGIN: @PTEST_PLUGIN@,rtegen
   OPT: -wp-prop=@check
   OPT: -wp-prop=-@check
*/
/* run.config_qualif
PLUGIN: wp,rtegen,report
   OPT: -wp-steps 5 -then -report
*/
//@ axiomatic A { predicate P reads \nothing ; }
void main() {
  //@check  c1: P;
  //@assert a1: P;
  //@check  c2: P;
  //@assert a2: P;
  ;
}
// note: eva and wp gives the same reporting
