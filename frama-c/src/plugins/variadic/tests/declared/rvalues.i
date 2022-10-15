int f(int a,...);

int main(){
  int x = 0;
  int i = f(1, 2+3, 4*5, &x);
  return i;
}
