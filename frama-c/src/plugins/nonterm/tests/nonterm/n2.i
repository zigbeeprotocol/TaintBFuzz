// non-terminating program

int main() {
  int i;
  int res = 0;
  for (i = 0; i < 10; i++) {
    Frama_C_show_each(i,res);
    res += i;
    i--;
  }
  return 0;
}
