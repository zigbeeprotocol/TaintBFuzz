/* run.config
* STDOPT: +"-slicing-level 2 -slice-pragma main -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
* STDOPT: +"-slicing-level 2 -slice-return main -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
*/


int tab[2]={0, 7 };
int G, X ;
typedef struct {int a; int b; } Ts;
Ts S;

int f(void) {
 volatile int i=0;
 int v;

 v = tab[i];

 G = X;

 return v;
}

int main(void) {
 int x = f();
 G += 1 ;
 //@ slice pragma expr G ;
 return x;
}
