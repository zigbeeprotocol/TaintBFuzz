/* run.config
   EXIT: 1
   STDOPT: #"-cpp-extra-args=-DALIGNAS"
   STDOPT: #"-cpp-extra-args=-DALIGNOF"
   STDOPT: #"-cpp-extra-args=-DCOMPLEX"
   STDOPT: #"-cpp-extra-args=-DGENERIC"
   STDOPT: #"-cpp-extra-args=-DIMAGINARY"
*/

#ifdef ALIGNAS
struct st_alignas {
  _Alignas(32) char buf[4];
};
#endif

int main(void) {
#ifdef ALIGNOF
  int alignd = _Alignof(double);
#endif

#ifdef COMPLEX
  double _Complex c = 1;
#endif

#ifdef GENERIC
  int generic = _Generic('0', char: 1, int: 2, default: 0);
#endif

#ifdef IMAGINARY
  //Note: GCC/Clang do not yet support _Imaginary
  double _Imaginary im = 0;
#endif

  return 0;
}
