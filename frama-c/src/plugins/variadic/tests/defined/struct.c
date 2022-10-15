#include <stdarg.h>

typedef struct {
  int left, top, right, bottom;
} rect;

int min(int a, int b)
{
  return a < b ? a : b;
}

int max(int a, int b)
{
  return a > b ? a : b;
}

// Compute the intersection of all rects
rect inter(int n, rect first, ...)
{
  rect ret = first, tmp;
  int i = 0;
  va_list list;
  va_start(list, first);

  for(i=1; i<n; i++){
    tmp = va_arg(list, rect);
    ret.left = max(ret.left, tmp.left);
    ret.top = max(ret.top, tmp.top);
    ret.right = min(ret.right, tmp.right);
    ret.bottom = min(ret.bottom, tmp.bottom);
  }

  va_end(list);
  return ret;
}

int main(){
  rect r;
  rect r1 = {10, 10, 50, 70};
  rect r2 = {0, 30, 20, 60};
  r = inter(2, r1, r2);
  return 0;
}
