/*run.config
PLUGIN: eva,inout,scope
  OPT: -eva -eva-verbose 0
 */

unsigned id(unsigned x) { return x; }

void main() {
  unsigned const r = id(1 > 2 ? 1 : 2);
  //@ assert written_r: r == 2;
}
