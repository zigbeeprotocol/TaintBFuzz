/* run.config
PLUGIN: @EVA_PLUGINS@
  STDOPT: +"-print"
*/
struct s {
  int a;
  char data[]; // FAM
};

int main() {
  struct s s1 = {0};
  return s1.a;
}
