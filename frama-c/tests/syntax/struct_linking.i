/* run.config
OPT: %{dep:@PTEST_NAME@_2.i} -print
*/
struct Foo {
  double z;
  int t;
  char u;
};

void g () {
  struct Foo g = { 0 };
  g.z = 36.0;
}
