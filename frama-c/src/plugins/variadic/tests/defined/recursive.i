/* run.config
STDOPT: +"-eva-unroll-recursive-calls 10"
*/
int f(int a, ...){
  if(a <= 0)
  	return 42;
  else
  	return f(a-1);
}

int main(){
  return  f(7);
}
