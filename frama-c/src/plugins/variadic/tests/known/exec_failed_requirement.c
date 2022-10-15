#include <unistd.h>

int main()
{
  // No argv but not completely wrong: the program will still crash there !
  // Value must find the problem
  execl("/bin/pwd", NULL);
}

