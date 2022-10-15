/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -eva @EVA_CONFIG@ -cpp-extra-args="-DPTEST"
   OPT: -machdep ppc_32 -eva @EVA_CONFIG@ -cpp-extra-args="-DPTEST"
*/

#ifndef PTEST
#include <stdio.h>
#endif

struct sbf { int c:16 ; unsigned int u:16 ;} bf ;
int main () {
  int int_inside_bitfield_is_unsigned ;
  bf.u --;
  bf.c --;
  int_inside_bitfield_is_unsigned = (bf.u > bf.c) ;

#ifndef PTEST
  printf("int_inside_bitfield_is_unsigned = %d\n",
         int_inside_bitfield_is_unsigned);
#endif
  return int_inside_bitfield_is_unsigned ;

}
