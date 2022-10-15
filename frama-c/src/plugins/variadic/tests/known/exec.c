#include <unistd.h>

int main()
{
  char *env[] = {"VAR=42", NULL};
  char *sentinel = NULL;

  // Simple test
  execle("/bin/sh", "sh", "-c", "echo $VAR", NULL, env);
  // Too many arguments but correct
  execl("ls", "ls", "-l", "--color", NULL, 42); 
  execlp("ls", "ls", "-all", NULL, NULL);
  execle("ls", "ls", NULL, env, 42, NULL);
  // Null present but not syntactically
  execlp("ls", "ls", "--reverse", sentinel);
}

