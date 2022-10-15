int main() {
  int i;
  int res = 0;
  for (i = 0; i < 10; i++) {
    for (int j = 2; j < 5; j++) {
      res += i;
      if (1) i++;
      if (i > 0) i--;
    }
    i--;
  }
  return 0;
}
