/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

/*@
	requires PROP_SUR_982: x>0;
	requires PROP_SUR_982: x+1>1;
	ensures PROP_SUR_982: x>0;
	ensures PROP_SUR_982: x+1>1;
*/
int f(int x);

void g(int a)
{
int c;
c = f(a);
}
