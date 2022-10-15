/* run.config
 MODULE: Change_formals
   OPT: -cpp-extra-args="-DNO_PROTO" -then-on test -print
   OPT: -cpp-extra-args="-DNO_IMPLEM" -then-on test -print
   OPT: -then-on test -print
*/

#ifndef NO_PROTO
int f(int x);
#endif

#ifndef NO_IMPLEM
int f(int x) { return x; }
#endif

// needed to prevent erasure of f in NO_IMPLEM case
int g() { return f(0); }
