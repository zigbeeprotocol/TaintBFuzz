/* run.config
   STDOPT: #" -rte-initialized=@all -print"
   STDOPT: #" -rte-initialized='@all,-f1' -print"
*/

int f1(void){
  int i = 0 ;
  return i ;
}
int f2(void){
  int i = 0 ;
  return i ;
}
