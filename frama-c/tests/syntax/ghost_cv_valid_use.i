typedef int int_array [10] ;

void instr(){
  //@ ghost int x ;
  //@ ghost int \ghost* p ;
  //@ ghost int arr[10] ;

  //@ ghost x = 1 ;
  //@ ghost *p = 1 ;
  //@ ghost arr[0] = 1 ;
}

void named(void){
  //@ ghost int_array a ;
  //@ ghost a[0] = 42 ;
}

struct Type {
  int field ;
} ;

void field_access(){
  struct Type ng_var ;
  //@ ghost struct Type g_var ;
  ng_var.field = 42 ;
  //@ ghost g_var.field = 42 ;
}

void nested(void){
  /*@ ghost
    int * * ptrp ;
    int * \ghost * ptrpg ;
    int \ghost * \ghost * ptrpgg ;

    int arra[10][10] ;

    int * arrp[10] ;
    int \ghost * arrpg[10] ;

    int (* ptra)[10] ;
    int \ghost (* ptrag) [10] ;
  */

  // ALLOWED
  /*@ ghost
    ptrp = 0 ;

    ptrpg = 0 ;
    *ptrpg = 0 ;

    ptrpgg = 0 ;
    *ptrpgg = 0 ;
    **ptrpgg = 1 ;

    arra[0][0] = 1 ;

    arrp[0] = 0 ;

    arrpg[0] = 0 ;
    *arrpg[0] = 1 ;

    ptra = 0 ;

    ptrag = 0 ;
    (*ptrag)[0] = 1 ;
  */
}

void assigns_clause(void){
  //@ ghost int *p ;

  /*@ loop assigns p, i ; */
  for(int i = 0; i < 10; i++);

  /*@ ghost
    /@ loop assigns p, i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ ghost
  /@ assigns *p ; @/
  void g_decl_star(int \ghost *p);

  /@ assigns *p ; @/
  void g_def_star(int \ghost *p){

  }
*/

// Note: this should be accepted as the pointer might point to a
// memory location which is indeed assigned by the actual code.

/*@ assigns *p ; */
void ng_decl_star(void) /*@ ghost (int \ghost *p) */ ;

/*@ assigns *p ; */
void ng_def_star(void) /*@ ghost (int \ghost *p) */ {

}

/*@ assigns *p ; */
void ng_decl_star_ng(void) /*@ ghost (int *p) */ ;

/*@ assigns *p ; */
void ng_def_star_ng(void) /*@ ghost (int *p) */ {

}

void assigns_loop_star(){
  //@ ghost int \ghost *p ;

  /*@ loop assigns *p, i ; */
  for(int i = 0; i < 10; i++);

  /*@ ghost
    /@ loop assigns *p, i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ ghost
  /@ assigns p[ 0 .. max ] ; @/
  void g_decl_set(int \ghost *p, int max);

  /@ assigns p[ 0 .. max ] ; @/
  void g_def_set(int \ghost *p, int max){

  }
*/

/*@ assigns p[ 0 .. max ] ; */
void ng_decl_set(int max) /*@ ghost (int \ghost *p) */ ;

/*@ assigns p[ 0 .. max ] ; */
void ng_def_set(int max) /*@ghost (int \ghost *p) */ {

}

/*@ assigns p[ 0 .. max ] ; */
void ng_decl_set_ng(int max) /*@ ghost (int \ghost *p) */ ;

/*@ assigns p[ 0 .. max ] ; */
void ng_def_set_ng(int max) /*@ghost (int \ghost *p) */ {

}

void assigns_loop_set(){
  //@ ghost int \ghost *p ;
  int max = 42 ;

  /*@ loop assigns p[ 0 .. max ], i ; */
  for(int i = 0; i < 10; i++);

  /*@ ghost
    /@ loop assigns p[ 0 .. max ], i ; @/
    for(int i = 0; i < 10; i++);
  */
}

/*@ ghost
  /@ assigns \nothing ; @/
  void ghost_decl_nothing(int * a) ;

  /@ assigns *a ; @/
  void ghost_decl_valid_a(int \ghost * a) ;

  void ghost_def_nothing(int * a){
    int x = *a ;
  }

  void ghost_def_valid_a(int \ghost * a){
    *a = 42 ;
  }
*/

void assigns_nothing_or_correct(void){
  int ng ;
  //@ ghost ghost_decl_nothing(&ng);
  //@ ghost ghost_def_nothing(&ng);



  //@ ghost int g ;
  //@ ghost ghost_decl_valid_a(&g);
  //@ ghost ghost_def_valid_a(&g);
}
