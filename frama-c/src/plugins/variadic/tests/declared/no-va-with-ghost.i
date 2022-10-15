int f(int a, int b, int c) /*@ ghost(int x) */;

int main(){
  return f(1, 2, 3) /*@ ghost(4) */;
}
