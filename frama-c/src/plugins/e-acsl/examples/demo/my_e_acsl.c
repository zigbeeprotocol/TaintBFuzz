#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#define LEN 10
int LAST[LEN] = { -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 };
int IDX = 0;

int mem(int x) {
  for(int i = 0; i < LEN; i++)
    if (LAST[i] == x) return x;
  return -1;
}

void e_acsl_assert(int predicate, 
		   char *kind, 
		   char *fct, 
		   char *pred_txt, 
		   int line) 
{
  if (! predicate) {
    if (mem(line) == -1) {
      LAST[IDX] = line;
      IDX++;
      int cpid = fork ();
      if (cpid < 0) {
	printf("%s failed at line %d of function %s.\n	\
The failing predicate is:\n%s.\n",
	       kind, line, fct, pred_txt);
      } else {
	int status;
	if (cpid == 0) {
	  char *line_string = (char*) malloc(sizeof(char)*3);
	  sprintf(line_string,"%d",line);
	  char *args[17] = { "frama-c", "-quiet", 
			     "-load", "demo.sav", "-save", "demo.sav",
			     "-load-module", "./Script", "-t2p-verbose", "1",
			     "-ppt-fct", fct,
			     "-ppt-name", kind,
			     "-ppt-line", line_string };
	  status = execvp("frama-c", args);
	  exit(status);
	} else
	  wait(&status);
      }
    }
  }
}
