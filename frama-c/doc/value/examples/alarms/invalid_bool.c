
union u_bool { _Bool b; unsigned char c; } ub;
void main () {
  ub.c = 42;
  _Bool b = ub.b;
}
