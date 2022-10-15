#include <wchar.h>
#include <stdio.h>

int main()
{
  wchar_t input[0x100] = L"forty-two is";
  wchar_t wstring[0x100];
  int i, j;

  //wprintf (L"%lc %lc\n", L'X', 88); /* requires intmax_t */
  wprintf (L"%d %ld\n", 42, 42L);
  wprintf (L"%10d %010d\n", 42, 42);
  wprintf (L"%d %x %o %#x %#o\n", 42, 42u, 42u, 42u, 42u);
  wprintf (L"%2.1f %+.0e %E\n", 42.0, 42.0, 42.0);
  wprintf (L"%*d \n", 4, 2);
  wprintf (L"%ls \n", L"42");

  swprintf (wstring, 0x100, L"%s = %d", L"42" " + " "42", 42 + 42);

  wscanf (L"%ls", wstring);
  wscanf (L"%d %d", &i, &j);

  swscanf (input, L"%ls %*s %d", wstring, &i);

  return 0;
}

