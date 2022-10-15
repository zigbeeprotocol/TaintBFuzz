int f(int a) {
  while (a);
  return 0;
}

int g(int b) {
  return f(!!b);
}

int main() {
  for (int i = 1; i < 2; i++) {
    g(i);
  }
  return 0;
}
