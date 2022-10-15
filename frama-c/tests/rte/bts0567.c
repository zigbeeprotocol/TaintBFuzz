/* run.config 
   STDOPT: #" -warn-signed-overflow -print"
*/

int tab [2] ;

//@ requires \valid(p+1) ;
void f(int *p) ;

void g(){
  f(tab) ;
}
