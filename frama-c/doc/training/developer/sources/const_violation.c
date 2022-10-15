const int Glob = 7;

int filter(int *x) {
  if (*x>Glob) return Glob;
  if (*x<0) return 0;
  return *x;
}

void incr(int *x) { (*x)++; }

int main(int argc, char* argv[]) {
  int y = 12;
  int *p = (argc<7) ? (int *)&Glob : &y;
  y = filter(p);
  if (argc > 5) incr(p);
  return y;
}

/*
Local Variables:
compile-command: "frama-c -load-script const_violation.ml const_violation.c"
End:
*/
