int f(int a,...) /*@ ghost(int x) */;

int main(){
  int x = 0;
  int i = f(1, 2+3, 4*5, &x) /*@ ghost(x+3) */;
  return i;
}
