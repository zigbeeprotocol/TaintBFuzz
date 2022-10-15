/* run.config
  OPT: -wp-msg-key refusage
*/
/* run.config_qualif
  DONTRUN:
*/

int a ;
int b ;

/*@ axiomatic A{
    logic int* get reads \nothing ;
    logic int* get_h = &a ;

    axiom a: get_h == get ;
    }

*/

/*@ axiomatic B{
  logic integer value reads \nothing ;
  axiom b: value == b ;
  }
*/

void foo(int* x){
  *x = a = b ;
}

/*@ requires a <= b ; */
int main(void){
  int e ;
  foo(&e) ;
}
