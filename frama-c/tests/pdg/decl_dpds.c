/* run.config
   
   STDOPT: +"-fct-pdg main"
*/

extern int G;

typedef struct {
  int a;
  int b;
} Tstr;

extern Tstr S;

int main (int argc, char *argv[4]) {
  int argc0 = argc++;
  int argc1 = argc;
  char c = argv[argc-1][0];
  argv[argc-1][0] = 'a';
  argc = 0;
  if (argc0) {
    int * p = &argc0;
    *p = *p + 1;
    }
  return argc0 + argc1 + G + S.a;
}
