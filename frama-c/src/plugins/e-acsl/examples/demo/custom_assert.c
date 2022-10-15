#include <stdio.h>

void e_acsl_assert(int predicate, 
		   char *kind, 
		   char *fct, 
		   char *pred_txt, 
		   int line) 
{
  if (! predicate) {
    FILE *f = fopen("log_file.log", "a");
    fprintf(f,
	    "%s failed at line %d in function %s.\n\
The failing predicate is:\n%s.\n",
	    kind, line, fct, pred_txt);
    fclose(f);
  }
}
