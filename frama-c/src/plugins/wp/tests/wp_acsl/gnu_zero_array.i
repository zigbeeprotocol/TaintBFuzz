/* run.config
   STDOPT: #"-rte -machdep gcc_x86_32"
*/
/* run.config_qualif
   STDOPT: #"-rte -machdep gcc_x86_32"
*/

/*@ assigns \result; */
void *alloc(void);

struct S { int fam[0]; };

int main (void) {
	struct S* s = alloc();
  return s->fam[0];
}
