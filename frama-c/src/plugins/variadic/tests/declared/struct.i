typedef struct {
  int a, b, c, d;
} s;

int f(int n, ...);

int main(){
  s s1 = {0, 1, 2, 3};
  s s2 = {4, 5, 6, 7};
  return f(2, s1, s2);
}
