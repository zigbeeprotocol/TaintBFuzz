int main(){
  {
    int a ;
  }
  ; // < NOP inserted
}

void f() {
  if (0) {
    int b;
  }
}

void h (int i) {
 int x = 1;
 int t[100 / sizeof(x)];
 int u[100 / sizeof(i)];
}

int c;
int g() { return 1 || (-1L || g(), c); }

int nop(void) {
  { int loc_var; }
  { int loc_var (void);
    return loc_var();
  }
}
