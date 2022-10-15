typedef void T(int, ...) /*@ ghost (int) */ ;
extern T f;

int main () {
  f(1, 2, 0) /*@ ghost(3) */;
  return 0;
}
