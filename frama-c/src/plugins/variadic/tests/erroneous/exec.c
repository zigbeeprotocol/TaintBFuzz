#include <unistd.h>

int main(){
  // Wrong argument type
  execl("ls", "ls", 42, NULL);
  // Missing NULL
  execlp("ls", "ls", "-l");
  // Missing env  
  execle("ls", "ls", "-l", NULL);
  // Wrong env
  execle("ls", "ls", "-l", NULL, 42);
}
