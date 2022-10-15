/* run.config
   COMMENT: Test the output of data contributing to an assertion.
*/
/* run.config_dev
   COMMENT: Print the data and filter the addresses of the output so that the test is deterministic.
   MACRO: ROOT_EACSL_GCC_OPTS_EXT --assert-print-data -e -DE_ACSL_DEBUG_ASSERT -F -no-unicode
   MACRO: ROOT_EACSL_EXEC_FILTER sed -e s/0x[0-9a-f]*$/0x000000/g
 */

#include <float.h>
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

void f() {}
void g() {}

struct A {
  int a;
};

union U {
  int a;
  float b;
};

int lvalue = 1;
int array1[] = {1, 2, 3, 4};
int array2[] = {5, 6};

enum EBool { EBOOL_MIN = (_Bool)0, EBOOL_MAX = (_Bool)1 };
enum EChar { ECHAR_MIN = (char)CHAR_MIN, ECHAR_MAX = (char)CHAR_MAX };
enum ESChar {
  ESCHAR_MIN = (signed char)SCHAR_MIN,
  ESCHAR_MAX = (signed char)SCHAR_MAX
};
enum EUChar {
  EUCHAR_MIN = (unsigned char)0,
  EUCHAR_MAX = (unsigned char)UCHAR_MAX
};
enum EInt { EINT_MIN = (int)INT_MIN, EINT_MAX = (int)INT_MAX };
enum EUInt { EUINT_MIN = (unsigned int)0, EUINT_MAX = (unsigned int)UINT_MAX };
enum EShort { ESHORT_MIN = (short)SHRT_MIN, ESHORT_MAX = (short)SHRT_MAX };
enum EUShort {
  EUSHORT_MIN = (unsigned short)0,
  EUSHORT_MAX = (unsigned short)USHRT_MAX
};
enum ELong { ELONG_MIN = (long)LONG_MIN, ELONG_MAX = (long)LONG_MAX };
enum EULong {
  EULONG_MIN = (unsigned long)0,
  EULONG_MAX = (unsigned long)ULONG_MAX
};
enum ELLong {
  ELLONG_MIN = (long long)LLONG_MIN,
  ELLONG_MAX = (long long)LLONG_MAX
};
enum EULLong {
  EULLONG_MIN = (unsigned long long)0,
  EULLONG_MAX = (unsigned long long)ULLONG_MAX
};

int main() {
  fprintf(stderr, "EVERY ASSERTION SHOULD PRINT ITS DATA IN EXECUTION LOG\n");

  // Integers
  // --------
  _Bool int_bool = 1;
  //@ assert \let x = int_bool; \true;
  char int_char = CHAR_MAX;
  //@ assert \let x = int_char; \true;
  signed char int_schar = SCHAR_MAX;
  //@ assert \let x = int_schar; \true;
  unsigned char int_uchar = UCHAR_MAX;
  //@ assert \let x = int_uchar; \true;
  int int_int = INT_MAX;
  //@ assert \let x = int_int; \true;
  unsigned int int_uint = UINT_MAX;
  //@ assert \let x = int_uint; \true;
  short int_short = SHRT_MAX;
  //@ assert \let x = int_short; \true;
  unsigned short int_ushort = USHRT_MAX;
  //@ assert \let x = int_ushort; \true;
  long int_long = LONG_MAX;
  //@ assert \let x = int_long; \true;
  unsigned long int_ulong = ULONG_MAX;
  //@ assert \let x = int_ulong; \true;
  long long int_llong = LLONG_MAX;
  //@ assert \let x = int_llong; \true;
  unsigned long long int_ullong = ULLONG_MAX;
  //@ assert \let x = int_ullong; \true;
  // MPZ
  //@ assert \let int_mpz = ULLONG_MAX + 1; int_mpz != ULLONG_MAX;

  // Reals
  // -----
  float real_float = FLT_MAX;
  //@ assert \let x = real_float; \true;
  double real_double = DBL_MAX;
  //@ assert \let x = real_double; \true;
  long double real_ldouble = LDBL_MAX;
  //@ assert \let x = real_ldouble; \true;
  // MPQ
  //@ assert \let real_mpq = 0.1; real_mpq != 1;

  // Pointer
  // -------
  void *ptr = &lvalue;
  //@ assert ptr != NULL;

  // Array
  // -----
  //@ assert array1 != array2;

  // Function
  // --------
  // FIXME: here f and g are pointers and not "functions"
  //@ assert f != g;

  // Structure
  // ---------
  struct A struct1 = {.a = 1};
  //@ assert \let x = struct1; \true;

  // Union
  // -----
  union U union1 = {.b = 1.};
  //@ assert \let x = union1; \true;

  // Enum
  // ----
  enum EBool enum_bool = EBOOL_MAX;
  //@ assert \let x = enum_bool; \true;
  enum EChar enum_char = ECHAR_MAX;
  //@ assert \let x = enum_char; \true;
  enum ESChar enum_schar = ESCHAR_MAX;
  //@ assert \let x = enum_schar; \true;
  enum EUChar enum_uchar = EUCHAR_MAX;
  //@ assert \let x = enum_uchar; \true;
  enum EInt enum_int = EINT_MAX;
  //@ assert \let x = enum_int; \true;
  enum EUInt enum_uint = EUINT_MAX;
  //@ assert \let x = enum_uint; \true;
  enum EShort enum_short = ESHORT_MAX;
  //@ assert \let x = enum_short; \true;
  enum EUShort enum_ushort = EUSHORT_MAX;
  //@ assert \let x = enum_ushort; \true;
  enum ELong enum_long = ELONG_MAX;
  //@ assert \let x = enum_long; \true;
  enum EULong enum_ulong = EULONG_MAX;
  //@ assert \let x = enum_ulong; \true;
  enum ELLong enum_llong = ELLONG_MAX;
  //@ assert \let x = enum_llong; \true;
  enum EULLong enum_ullong = EULLONG_MAX;
  //@ assert \let x = enum_ullong; \true;

  // Deduplication
  // -------------
  int a = 2;
  int b = 3;
  //@ assert \let c = a + b; a != b && c == a + b;

  return 0;
}
