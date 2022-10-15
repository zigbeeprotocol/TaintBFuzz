/* run.config
  COMMENT: -e-acsl-builtins
  STDOPT: #"-e-acsl-builtins incr"
*/
/* run.config_dev
  MACRO: ROOT_EACSL_GCC_FC_EXTRA_EXT -e-acsl-builtins incr
*/

int incr(int);

/*@ ensures \result == incr(i); */
int f(int i) {
  int j = i + 1;
  return j;
}

int incr(int x) {
  return x + 1;
}

int main() {
  int i = f(2);
  return 0;
}
