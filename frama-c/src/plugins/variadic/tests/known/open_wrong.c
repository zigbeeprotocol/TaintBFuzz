/* A note on this test. 
   The mechanism choosing the version of open to use will conclude that, since
   a string is not a possible argument, the function call has probably too
   many parameters. The problem and the warning message issued by the
   plug-in is not very intuitive.
 */

#include <fcntl.h>

int main(){
  char* file = "file";
  int flag = 0;
  open(file, flag, "");
  return 0;
}
