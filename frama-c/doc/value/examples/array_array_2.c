int t[10][10];

int main() {
  int *p=&t[0][12];
  return *p;
}
