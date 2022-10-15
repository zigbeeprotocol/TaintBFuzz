extern void * f1();
extern void f2(int);

void main(int c) {
  int * (*p)(int);
  void *x, *y;

  p = &f1;
  x = (*p)(c); // Alarm, but the analysis proceeds

  p = &f2;
  y = (*p)(c); // Call deemed entirely invalid
}
