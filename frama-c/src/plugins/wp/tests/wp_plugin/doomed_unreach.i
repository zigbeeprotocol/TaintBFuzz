/* run.config
   DONTRUN:
 */

/* run.config_qualif
   OPT: -wp-smoke-tests -wp-steps 100
*/

//@ assigns \result;
int job(int x) {
  switch(x) {
    return 42;
  case 0:
    return 0;
  case 1:
    return 1;
    x = 42;
    return 42;
  default:
    return 3;
  }
  x = 42;
  return 42;
}
