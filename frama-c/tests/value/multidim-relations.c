/* run.config*
   STDOPT: #"-eva-msg-key d-multidim -eva-domains multidim -eva-plevel 1 -eva-multidim-disjunctive-invariants"
*/
#include <__fc_builtin.h>

typedef struct {
  char kind;
  double value;
  int *ptr;
} s;

#define MAX 350

s t[MAX];
int g = 0, h = 1;

void init_array (void) {
  for (int i = 0; i < MAX; i++) {
    t[i].kind = 1;
    t[i].value = (double)i * 11.;
    t[i].ptr = i%2 ? &g : &h;
  }
}

void set_null (int i) {
  t[i].kind = 0;
  t[i].ptr = 0;
}

void use_array (int index) {
  int result = *t[index].ptr; // should be valid.
}

void main () {
  init_array();
  set_null (57);
  set_null (141);
  int index = Frama_C_interval(0, MAX-1);
  if (t[index].kind != 0)
    use_array(index);
}
