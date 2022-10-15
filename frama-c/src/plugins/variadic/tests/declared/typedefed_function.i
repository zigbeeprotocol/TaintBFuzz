typedef void T(int, ...);
extern T f;

int main () {
  f(1, 2, 0);
  return 0;
}
