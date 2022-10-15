/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

/*@ allocates \result;
  @ ensures  \result==\null || \fresh(\result,10);
*/
char* my_malloc (unsigned int n) ;

int main() {
  
  //@ requires \true ; 
  char * p = my_malloc (10) ;
  if (p) return 1;
  return 0;

}
