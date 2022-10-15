/* run.config
   OPT:-wp-gen -wp-prover=why3 -wp-msg-key=print-generated
*/
/* run.config_qualif
   DONTRUN:
*/

struct S { int f ; unsigned a[5] ; long b[5] ; };

/*@ ensures *p == \old(*p) ; */
void job(struct S *p, int v)
{
	p->f = v;
}
