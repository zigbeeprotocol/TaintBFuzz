/* run.config
 MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

//@ assigns \nothing;
void g (void) ;

//@ assigns \nothing;
void f () { g(); }

