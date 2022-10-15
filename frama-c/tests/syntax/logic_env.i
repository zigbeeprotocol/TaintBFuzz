/* run.config
 MODULE: logic_env_script
   OPT: -no-autoload-plugins
*/

//@ predicate foo(integer x) = x == 0;

int X;

//@ predicate bar{L} = X == 0;
