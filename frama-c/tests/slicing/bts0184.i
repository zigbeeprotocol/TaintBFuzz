/* run.config
   STDOPT: +"-slice-pragma x  -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
 **/
int x(int y, int z)
{
/*@ slice pragma expr y == 1; */
//@ assert y == 1;
//@ assert y + z == 3;
 return y;
}

int main()
{
 return 0;
}

int z1()
{
 return x(2,2);
}
