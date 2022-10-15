/* run.config
  OPT: -instantiate
*/
void foo(void (* bar)()){
  (*bar)();
}
