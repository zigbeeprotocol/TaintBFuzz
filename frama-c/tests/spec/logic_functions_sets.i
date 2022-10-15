/* run.config
   MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

/*@
  logic set<integer> constant_1(integer n) = 1 ;
  logic set<integer> constant_2(integer n) = { 1 } ;
  logic set<integer> with_sub_1(integer n) = (n < 0) ? 1 : 2 ;
  logic set<integer> with_sub_2(integer n) = (n < 0) ? 1 : { 2 } ;
*/
