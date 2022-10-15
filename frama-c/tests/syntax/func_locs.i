/* run.config
 MODULE: @PTEST_NAME@
   STDOPT: +"-no-print"
*/


//@ assigns \nothing;
void with_spec() {
}

int gx;

/*@
  requires req: a >= 0 || gx == 0;
  assigns \result \from a;
  ensures ens: \result == a;
 */
int id(int a);

/*@
  requires req: a >= 0;
*/
int id(int a);

int decl_no_spec(); int id(int a);

int def_no_spec() {
  return 2;
}

/*@
  requires \true;
*/
int main() {
  return 0;
}
