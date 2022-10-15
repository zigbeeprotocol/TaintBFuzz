/* run.config*
   STDOPT: #"-eva-msg-key pointer-comparison"
   STDOPT: #"-eva-undefined-pointer-comparison-propagate-all -eva-msg-key pointer-comparison"
*/

int a;

char *p = &a;
int *q = &a;

typedef unsigned int size_t;

int main() {
  if ( (p + (size_t) -5) < p ) Frama_C_show_each_1(); else Frama_C_show_each_2();
  if ( (q + (size_t) -5) < q ) Frama_C_show_each_3(); else Frama_C_show_each_4();
}
