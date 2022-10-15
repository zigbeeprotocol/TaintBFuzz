volatile int nondet;

int nt(int v) {
  while (1);
}

int f(int v) {
  if (v) return nt(v);
  else return nt(nondet);
}

int g(int v) {
  if (v) return f(v);
  else return f(nondet);
}

int h(int v) {
  if (v) return g(v);
  else return g(nondet);
}

int main(int v) {
  if (v) return h(v);
  else return g(nondet);
}
