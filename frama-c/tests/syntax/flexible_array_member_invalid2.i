/* run.config*
 EXIT: 1
   STDOPT:
*/

// invalid flexible array member (two incomplete fields)
struct s {
  int len;
  char data[];
  char more_data[];
} ss;
