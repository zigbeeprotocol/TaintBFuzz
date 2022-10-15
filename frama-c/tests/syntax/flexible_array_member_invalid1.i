/* run.config
 EXIT: 1
   STDOPT:
*/

// invalid flexible array member (empty struct otherwise)
struct s1 {
  char data[];
} ss1;
