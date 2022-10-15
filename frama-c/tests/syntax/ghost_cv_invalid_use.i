/* run.config*
 EXIT: 1
   STDOPT:
*/
// In this file, each write raises an error: writing non-ghost memory location
// from ghost code, except if a comment says the opposite.

struct Type {
  int field ;
} ;

void direct(void){
  int ng ;
  /*@ ghost ng = 42 ; */
}

void ptr_access(void){
  int ng ;
  //@ ghost int * ptr = &ng ;
  //@ ghost *ptr = 42 ;
}

void in_struct(void){
  struct Type ng_var ;
  //@ ghost ng_var.field = 42 ;
}

void nesting(void){
  /*@ ghost
    int * * ptrp ;
    int * \ghost * ptrpg ;
    int * arrp[10] ;
    int (* ptra)[10] ;
  */

  /*@ ghost
   *ptrp = (void *) 0 ;
   **ptrp = 1 ;
   **ptrpg = 1 ;
   *arrp[0] = 1 ;
   (*ptra)[0] = 1 ;
  */
}

/*@ ghost
  /@ assigns *a ; @/
  void decl_invalid_a(int * a) ;

  void decl_invalid_no_assigns (void);
*/

/*@ ghost
  void def_invalid_a(int * a){
    *a = 42 ;
    decl_invalid_a(a); // should not raise an error as the problem is in `decl_invalid_a`
  }
*/

void assigns_clause(void){
  int p ;

  /*@ ghost
    /@ loop assigns p, i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ ghost
  /@ assigns *p ; @/
  void g_decl_star(int *p);

  /@ assigns *p ; @/
  void g_def_star(int *p){

  }
*/

void assigns_loop_star(){
  //@ ghost int *p ;

  /*@ ghost
    /@ loop assigns *p, i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ ghost
  /@ assigns p[ 0 .. max ] ; @/
  void g_decl_set(int *p, int max);

  /@ assigns p[ 0 .. max ] ; @/
  void g_def_set(int *p, int max){

  }
*/

void assigns_loop_set(){
  //@ ghost int *p ;
  int max = 10 ; // this is valid

  /*@ ghost
    /@ loop assigns p[ 0 .. max ], i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ assigns *a ; */
void assigns_parameter(int* a);

void no_assign_specification(int* a);

/*@ assigns *a ; */
int int_assigns_parameter(int* a);

int int_no_assign_specification(int* a);

void def_no_assign_spec(void){

}
int int_def_no_assign_spec(void){
  return 42;
}

void calls(void){
  int ng ;
  /*@ ghost
    assigns_parameter(&ng);
    no_assign_specification(&ng);
    def_no_assign_spec();
  */
  /*@ ghost
    int x1 = int_assigns_parameter(&ng);
    int x2 = int_no_assign_specification(&ng);
    int x3 = int_def_no_assign_spec();
  */
}

/*@ assigns \nothing ; */
void assigns_nothing(int* a);

/*@ assigns \nothing ; */
int int_assigns_nothing(int* a);

/*@ assigns *a ; */
void assigns_parameter(int* a);

/*@ assigns *a ; */
int int_assigns_parameter(int* a);

void ghost_calls_to_non_ghost_functions(){
  int ng ;
  //@ ghost int g ;

  /*@ ghost
    assigns_nothing(&ng);
    assigns_nothing(&g);
    assigns_parameter(&g);
  */
  /*@ ghost
    int x1 = int_assigns_nothing(&ng);
    int x2 = int_assigns_nothing(&g);
    int x3 = int_assigns_parameter(&g);
  */
}
