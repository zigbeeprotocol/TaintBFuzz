/* run.config*
   STDOPT:
 EXIT: 1
   STDOPT: #"-cpp-extra-args=-DFUNTYPE"
   STDOPT: #"-cpp-extra-args=-DNEG1"
   STDOPT: #"-cpp-extra-args=-DNEG2"
   STDOPT: #"-cpp-extra-args=-DNAMEDZERO"
*/

#ifdef FUNTYPE
// invalid field with function type, parsing should fail
struct {
  void f(int);
} s;
#endif

// negative-width bitfields, parsing should fail
struct neg_bf
{
#ifdef NEG1
  int a:(-1); // invalid
#endif
#ifdef NEG2
  int b:(-2147483647-1); // invalid
#endif
#ifdef NAMEDZERO
  int d:(-0); // invalid (named zero-width)
#endif
  int :(-0); // valid (unnamed zero-width)
};
