/* run.config
PLUGIN: variadic
 MODULE: @PTEST_NAME@
   OPT: -print -variadic-no-translation
*/
#include <stdio.h>
// See http://stackoverflow.com/questions/18102502/mixing-wide-and-narrow-string-literals-in-c
int main(){
printf( "%s\n", "123" "456" );
printf( "%ls\n", L"123" L"456" );
printf( "%ls\n", "123" L"456" );
printf( "%ls\n", L"123" "456" );
printf( "%ls\n", L"123" L"456" );
return 0;
}
