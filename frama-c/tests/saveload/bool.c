/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
   EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -save @PTEST_NAME@.sav -machdep x86_32 -eva @EVA_OPTIONS@ @PTEST_FILE@ > @PTEST_NAME@_sav.res 2> @PTEST_NAME@_sav.err
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav} -out -input -deps"
   STDOPT: +"-load %{dep:@PTEST_NAME@.sav} -eva @EVA_OPTIONS@"
 */

#include "stdbool.h"
#include "stdio.h"

bool x;
int y;

int f() {
  int i, j;

  i = 10;
  /*@ assert (i == 10); */
  while(i--);
  j = 5;

  return 0;
}

int main() {
  f();
  x=false;
  printf("%d\n",x);
  x=2;
  printf("%d\n",x);
  y=x+1;
  printf("%d,%d\n",x,y);
  x=x+1;
  printf("%d\n",x);
  x=x+1;
  printf("%d\n",x);
  return y;
}
