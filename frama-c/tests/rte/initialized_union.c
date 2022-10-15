/* run.config
   STDOPT: #" -rte-initialized=@all -warn-signed-overflow -print"
   STDOPT: #" -cpp-extra-args=-DEMPTY -machdep gcc_x86_64 -rte-initialized=@all -warn-signed-overflow -print"
*/

union U {
  char c;
  int i;
  double f;
};

union U2 {
  int i1;
  int i2;
};

union U3 {
  union U u;
  union U2 u2;
};

struct S {
  union U u;
};

union U u_global;
#ifdef EMPTY
// supported by Frama-C
union empty {};
#endif
int main(){

  union U u_local1;
  union U u_local2;

  union U2 u2_local1;
  union U2 u2_local2;

  union U3 u3_local1;
  union U3 u3_local2;
#ifdef EMPTY
  union empty e;
#endif
  u_local1.c = 1;

  u_local2 = u_local1;

  u2_local1.i2 = u_local1.i;

  u2_local2 = u2_local1;

  u3_local1.u = u_local1;

  u3_local2 = u3_local1;

  double f = u_global.f;

  struct S s1, s2;
  s1.u.c = 'a';
  s2.u = s1.u;
#ifdef EMPTY
  union empty e1 = e;
#endif
  return 0;
}
