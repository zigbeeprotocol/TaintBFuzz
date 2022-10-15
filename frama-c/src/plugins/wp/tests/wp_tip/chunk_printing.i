/* run.config
   OPT: -wp-rte -wp-msg-key state
*/
/* run.config_qualif
   DONTRUN:
*/

struct V {
	int* a ;
	unsigned* b ;
};

struct V* y ;

/*@
	assigns \nothing;
	ensures \result == v->a || \result == y->a;
*/
int* get_int(struct V* v);

/*@
	assigns \nothing;
	ensures \result == v->b || \result == y->b;
*/
unsigned* get_uint(struct V* v);

int main(void){
	struct V x ;
	x.a = get_int(&x);
	x.b = get_uint(&x);

	//@ assert *(x.a) == *(x.b);
}
