/* run.config
DONTRUN: main entry of test is in struct_linking.i
*/
struct Foo {
int x; double y;
};

void f() {
  struct Foo f = { 0 };
  f.y = 42.0;
}
