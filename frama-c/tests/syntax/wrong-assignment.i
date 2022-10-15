/* run.config*
 EXIT: 1
  STDOPT:
*/


typedef struct { _Bool a; } ebool;

ebool b, c;

void d() {
  // this assignment should be rejected
  c.a = b;
}
