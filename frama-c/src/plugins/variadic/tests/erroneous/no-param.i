/* run.config*
 EXIT: 1
   STDOPT:
*/
void f(...) // f must have at least one argument
{
  return;
}

int main()
{
  f(0);
}
