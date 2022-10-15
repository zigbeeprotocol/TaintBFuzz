/* run.config
   PLUGIN: @EVA_PLUGINS@
   EXIT: 1
   STDOPT: #"-cpp-extra-args=-DBITFIELD"
   STDOPT: #"-cpp-extra-args=-DARRAY_DECL"
   STDOPT: #"-cpp-extra-args=-DCASE_RANGE"
   STDOPT: #"-cpp-extra-args=-DCASE_RANGE2"
   STDOPT: #"-cpp-extra-args=-DINIT_DESIGNATOR"
   STDOPT: #"-cpp-extra-args=-DINIT_DESIGNATOR2"
   STDOPT: #"-cpp-extra-args=-DRANGE_DESIGNATOR"
   STDOPT: #"-cpp-extra-args=-DRANGE_DESIGNATOR2"
   STDOPT: #"-cpp-extra-args=-DATTRIBUTE_CONSTANT"
   STDOPT: #"-cpp-extra-args=-DLOGIC_CONSTANT"
   STDOPT: #"-cpp-extra-args=-DLOGIC_CONSTANT_OCTAL"
   STDOPT: #"-cpp-extra-args=-DEVA_UNROLL -eva -kernel-warn-key annot-error=error"
   STDOPT: #"-cpp-extra-args=-DCABS_DOWHILE"
   STDOPT: #"-cpp-extra-args=-DARRAY_INIT1"
   STDOPT: #"-cpp-extra-args=-DARRAY_INIT2"
   STDOPT: #"-cpp-extra-args=-DARRAY_INIT3"
   STDOPT: #"-cpp-extra-args=-DARRAY_INIT4"
   EXIT: 0
   STDOPT: #"-cpp-extra-args=-DUNROLL_PRAGMA"
*/







// Lines intentionally left blank to minimize future oracle changes

volatile int nondet;
#ifdef BITFIELD
struct st {
  int bf:(999999999999999999U+9999999999999999999U);
};
#endif

#ifdef ARRAY_DECL
int arr[9999999999999999999U+18000000000000000000U];
char arr1[99999999999999999999U];
#endif

#ifdef CASE_RANGE
unsigned long nondetul;
void case_range() {
  switch (nondetul)
  case 0 ... 9999999999999999999U:;
  case 0 ... 199999999999999999U:;
}
#endif

#ifdef CASE_RANGE2
void case_range2() {
  switch (nondet)
  case 0 ... 10000000U:;
}
#endif

#ifdef INIT_DESIGNATOR
int arr2[9999999999999999999U] = { [9999999999999999999U] = 42 };
#endif

#ifdef INIT_DESIGNATOR2
int arr3[1] = { [9999999999999999999U] = 42 };
#endif

#ifdef RANGE_DESIGNATOR
int arr4[1] = { [-9999999999999999999U ... 9999999999999999999U] = 42 };
#endif

#ifdef RANGE_DESIGNATOR2
int widths[] = { [99999999999999999 ... 999999999999999999] = 2 };
#endif


#ifdef ATTRIBUTE_CONSTANT
struct acst {
  int a __attribute__((aligned(0x80000000000000000)));
};
#endif

typedef struct {
  char a;
  int b __attribute__((aligned(0x8000000000000000)));
  double c __attribute__((aligned(0x8000000000000000+0x8000000000000000)));
} stt ;

//@ logic integer too_large_integer = 9999999999999999999;

#ifdef LOGIC_CONSTANT
//@ type too_large_logic_array = int[9999999999999999999U];
#endif

#ifdef LOGIC_CONSTANT_OCTAL
//@ type too_large_logic_array_octal = int[09876543210];
#endif

#ifdef ARRAY_INIT1
// Previously caused Invalid_argument(Array.make)
int a1[] = {[72057594037927936] = 0};
#endif

#ifdef ARRAY_INIT2
struct arri2 {
  int a[7205759403792795];
};
struct st {
  struct arri2 a;
};
// Previously caused Out of memory
struct st s = {
  {{[7205759403792793 ... 7205759403792793] = 0}}
};
#endif

#ifdef ARRAY_INIT3
int ai3[] = {0xdead, [72057594037927936] = 0xbeef};
#endif
#ifdef ARRAY_INIT4
// Previously caused Out of memory
int ai4[] = {1, [7205759403792793] = 11};
#endif

int main() {
#ifdef EVA_UNROLL
  //@ loop unroll (-9999999999999999999); // IntLimit
  while (nondet);
  //@ loop unroll too_large_integer; // ExpLimit
  while (nondet);
  //@ slevel 9999999999999999999;
  while (nondet);
#endif
#ifdef CABS_DOWHILE
  do { } while (09);
#endif
#ifdef UNROLL_PRAGMA
  //@ loop pragma UNROLL 99999999999999999999;
#endif
  while (nondet);
  return 0;
}
