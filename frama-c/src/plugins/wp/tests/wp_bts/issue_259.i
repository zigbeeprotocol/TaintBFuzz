/*@ assigns \nothing; */
int f(int *p) { return *p; }

/*@ assigns \nothing; */
int g(int *p, int c) {
  switch (c) {
  case 0:
    if (f(p)) return 1;
  default:
    return 0;
  }
}
