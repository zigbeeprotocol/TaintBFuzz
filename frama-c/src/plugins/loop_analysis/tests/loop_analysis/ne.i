void a1() {
  for (int i = 3; i + 4 != 50; i++); // i IN [3..45] (43)
}

void a2() {
  for (int i = -100; i + 4 != 50; i++); // i IN [-100..45] (146)
}

void a3() {
  for (int i = 3; i - 4 != 50; i++); // i IN [3..53] (51)
}

void a4() {
  for (int i = -100; i - 4 != 50; i++); // i IN [-100..53] (154)
}

void a5() {
  for (int i = 100; i + 4 != 50; i--); // i IN [55..100] (46)
}

void a6() {
  for (int i = -100; i + 4 != -150; i--); // i IN [-145..-100] (46)
}

void a7() {
  for (int i = 100; i - 4 != 50; i--); // i IN [47..100] (54)
}

void a8() {
  for (int i = -100; i - 4 != -150; i--); // i IN [-153..-100] (54)
}

void f01() { // OK (4)
  for(int i = 0; i != 8; i+=2);
}

void f02() { // infinite loop
  for(int i = 1; i != 8; i+=2);
}

void f03() { // OK (4)
  for(int i = 8; i != 0; i-=2);
}

void f04() { // infinite loop
  for(int i = 9; i != 0; i-=2);
}

void f05() { // OK (1)
  for(int i = 10; i + 5 != 30; i+=15);
}

void f06() { // infinite loop
  for(int i = 7; i + 5 != 30; i+=15);
}

void f07() { // OK (1)
  for(int i = 30; i - 5 != 10; i-=15);
}

void f08() { // infinite loop
  for(int i = 20; i - 5 != 10; i-=15);
}

void f09() { // OK (1)
  for(int i = -10; i != -8; i+=2);
}

void f10() { // infinite loop
  for(int i = -11; i != -8; i+=2);
}

void f11() { // OK (6)
  for(int i = -8; i != -20; i-=2);
}

void f12() { // infinite loop
  for(int i = -9; i != -20; i-=2);
}

void f13() { // OK (4)
  for(int i = -100; i + 5 != -35; i+=15);
}

void f14() { // infinite loop
  for(int i = -70; i + 5 != -40; i+=15);
}

void f15() { // OK (1)
  for(int i = -20; i - 5 != -40; i-=15);
}

void f16() { // infinite loop
  for(int i = -20; i - 5 != -60; i-=15);
}


void no_iter01() {
  for(int i = 0; i != 8; i-=2);
}

void no_iter02() {
  for(int i = 1; i != 8; i-=2);
}

void no_iter03() {
  for(int i = 8; i != 0; i+=2);
}

void no_iter04() {
  for(int i = 9; i != 0; i+=2);
}

void no_iter05() {
  for(int i = 10; i + 5 != 30; i-=15);
}

void no_iter06() {
  for(int i = 7; i + 5 != 30; i-=15);
}

void no_iter07() {
  for(int i = 30; i - 5 != 10; i+=15);
}

void no_iter08() {
  for(int i = 20; i - 5 != 10; i+=15);
}

int main() {
  return 0;
}
