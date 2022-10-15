/* run.config*
OPT: -slice-pragma main -then-last -print
*/
int g(int x) { return x; }

int main() {
  /*@ assert &g == &g; */
  /*@ slice pragma stmt; */
  g(0);
}
