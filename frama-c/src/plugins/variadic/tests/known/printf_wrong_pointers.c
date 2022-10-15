#include <stdio.h>

int main(){
  signed short tt;
  unsigned int ui = 42;
  char *string = "foo";
  wchar_t *wstring = L"bar";

  volatile nondet = 0;

  // Wrong pointers are passed to printf and this must be detected by value
  switch (nondet)
  {
  case 0: printf("%n", &tt); // Wrong size
  case 1: printf("%n", &ui); // Wrong signedness
  case 2: printf("%hhn", string); // Wrong size
  case 3: printf("%s", wstring); // Wrong char size
  case 4: printf("%ls", string); // Wrong char size
  }
}
