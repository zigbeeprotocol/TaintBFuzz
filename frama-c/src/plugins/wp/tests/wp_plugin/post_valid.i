int global;

int *p_global, *p_local, *p_formal ;

/*@
  ensures LOCAL: !\valid(p_local);
  ensures FORMAL: \valid(p_formal); // FAILS
  ensures GLOBAL: \valid(p_global);
*/
void job(int formal) {
  int local = formal;
  p_local = &local;
  p_global = &global;
  p_formal = &formal;
}
