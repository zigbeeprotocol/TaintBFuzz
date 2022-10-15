#include <wchar.h>
#include <stdio.h>

volatile int nondet;

int main() {
  wchar_t data[100];
  wmemset(data, L'A', 99);
  data[99] = L'\0';
  wchar_t dest[50] = L"";
  if (nondet) {
    swprintf(dest, wcslen(data), L"%ls", data); // must fail
    //@ assert \false;
  }
  swprintf(dest, wcslen(data)/2, L"%ls", data); // ok
  return 0;
}
