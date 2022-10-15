/* run.config
 MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

/*@ type foo = A | B; */

/*@ logic foo f(integer x) = x>=0 ? A : B; */
