/* run.config
   STDOPT: #""
   EXIT: 1
   STDOPT: #"-cpp-extra-args=-DMULTIVLA"
*/

const int n = 10;

void main() {
  int a[n][42]; // single variable length dimension
  a[0][0] = 1;
  int b[a[0][0]][5][10]; // idem
#ifdef MULTIVLA
  // arrays with non-first variable dimensions; not currently supported
  int c[n][n];
  int d[42][n];
  int e[1][n][9];
#endif
}
