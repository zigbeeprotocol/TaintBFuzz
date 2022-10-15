/* run.config
STDOPT: +"-then -variadic-no-translation -then -variadic-translation -variadic-no-strict"
*/

typedef enum { OK, ERROR } RC;
#include <stdio.h>

int main(){
  int i = 42;
  unsigned int ui = 42;
  long int li = 42;
  unsigned long int uli = 42;  
  char c = '4';
  float f = 42.0f;
  long double ld = 42.0l;
  char *string = "42";

  printf("%hhd", c); // Promotion makes this ok
  printf("%d", ui); // Wrong signedness
  printf("%x", i); // Wrong signedness
  printf("%ld", i); // Wrong strictness
  printf("%d", li); // Wrong strictness
  printf("%lu", ui); // Wrong strictness
  printf("%u", uli); // Wrong strictness
  printf("%p", ui); // Wrong type
  printf("%f", f); // Promotion makes this ok
  printf("%f", ld); // Type too large
  printf("%lf", ld); // Type too large
  printf("%Lf", f); // Type too short
  printf("%s", i); // Wrong type
  printf("%d", string); // Wrong type


  RC rc = OK;
  printf("%u", rc); // Correct type with '-enums gcc-enums'
  printf("%d", rc); // Wrong type (in strict mode)
}
