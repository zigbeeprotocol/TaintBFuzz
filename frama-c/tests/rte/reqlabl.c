/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

//@ requires PROP_SUR_982: x>0;
int f(int x);

void g(int a)
{
int c;
c = f(a);
} 
