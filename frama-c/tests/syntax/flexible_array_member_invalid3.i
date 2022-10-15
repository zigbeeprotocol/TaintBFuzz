/* run.config*
 EXIT: 1
   STDOPT:
*/


// invalid flexible array member (two incomplete fields in same field group)
struct s {
  int len;
  char data[], more_data[];
} ss;
