struct S { char a; int b; } s = { 'a' , 3 } ;
char main(void)
{
  return ((char*)&s)[1];
}
