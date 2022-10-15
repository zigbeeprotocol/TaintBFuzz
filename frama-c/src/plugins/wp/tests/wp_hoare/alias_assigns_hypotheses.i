/* run.config
   OPT:
   OPT:-wp-no-warn-memory-model -wp-check-memory-model -then -print
*/

/* run.config_qualif
	 DONT_RUN:
*/

int global[1];
int *g_alias;

/*@ requires \valid(g_alias);
    assigns *g_alias;
    ensures *g_alias == 1;
    ensures \old(global[0]) == global[0]; */
void global_alias(void) {
	*g_alias = 1;
}

/*@ requires \valid(g_alias);
    assigns *g_alias;
    ensures *g_alias == 1; */
void global_no_alias(void) {
	*g_alias = 1;
}

/*@ requires \valid(f_alias);
    assigns *f_alias;
    ensures *f_alias == 1;
    ensures \old(global[0]) == global[0]; */
void formal_alias(int* f_alias) {
	*f_alias = 1;
}

/*@ requires \valid(f_alias);
    assigns *f_alias;
    ensures *f_alias == 1; */
void formal_no_alias(int* f_alias) {
	*f_alias = 1;
}

/*@ requires \valid(alias_array);
    assigns (*alias_array)[0 .. 1];
    ensures (*alias_array)[0] == 1;
    ensures (*alias_array)[1] == 1;
    ensures \old(global[0]) == global[0]; */
void formal_alias_array(int (*alias_array)[2]){
  (*alias_array)[0] = 1;
  (*alias_array)[1] = 1;
}

// With field

struct X { int x; };

/*@ requires \valid(x);
    assigns x->x ;
    ensures x->x == 1;
    ensures \old(global[0]) == global[0]; */
void field_alias(struct X* x){
  x->x = 1 ;
}

// With field, via set

// Through set:

/*@ requires \valid(x);
    assigns x[0..3].x ;
    ensures x->x == 1;
    ensures \old(global[0]) == global[0]; */
void field_range_alias(struct X* x){
  x->x = 1 ;
}

/*@ requires \valid(g_alias);
    assigns { *g_alias, *f_alias } ;
    ensures *g_alias == 1;
    ensures \old(global[0]) == global[0]; */
void set_alias(int *f_alias) {
  *g_alias = 1;
}


// Through comprehension:

/*@ requires \valid(g_alias);
    assigns { *alias | int* alias ; alias == \at(g_alias, Pre) } ;
    ensures *g_alias == 1;
    ensures \old(global[0]) == global[0]; */
void comprehension_alias(void) {
  *g_alias = 1;
}

// Through union:

/*@ requires \valid(g_alias);
    assigns \union(*g_alias, *f_alias) ;
    ensures *g_alias == 1;
    ensures \old(global[0]) == global[0]; */
void union_alias(int *f_alias) {
  *g_alias = 1;
}
