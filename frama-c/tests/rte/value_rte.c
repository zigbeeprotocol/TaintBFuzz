/* run.config
PLUGIN: @PTEST_PLUGIN@ eva,inout,scope report
STDOPT: +"-then -eva @EVA_OPTIONS@ -then -report"
*/
#include "stdio.h"

int main(){
  int t[5] = {1,2,3,4,5};
  int cpt =0 ;
  int tmp ;
  while (cpt<10){
    tmp = getchar() ;
    if ( t[cpt] > tmp )
      { return 1 ; }
    cpt++ ;
  }
  return 10 ;
}
