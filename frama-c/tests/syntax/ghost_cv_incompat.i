/* run.config*
 EXIT: 1
   STDOPT:
*/

typedef int int_array [10] ;
struct Type { int field ; } ;

void decl_ghost(void) /*@ ghost (int \ghost * p) */ ;
void def_ghost(void) /*@ ghost (int \ghost * p) */ {}

void decl_not_ghost(void) /*@ ghost (int * p) */ ;
void def_not_ghost(void) /*@ ghost (int * p) */ {}

/*@
  ghost
  /@ assigns \nothing ; @/
  int * function(void) ;
*/

//
// Non-ghost -> Ghost
//

int ng ;
//@ ghost int * gl_gp ;
//@ ghost int \ghost * gl_gpg_1 = &ng ;   // error: address of non-ghost integer into pointer to ghost
//@ ghost int \ghost * gl_gpg_2 = gl_gp ; // error: pointer to a non-ghost location into pointer to ghost


int *gl_p00, *gl_p01 ;
// error: we transform pointer to non-ghost into pointer to ghosts
//@ ghost int \ghost * gl_array[3] = { gl_p00, gl_p00, gl_p01 };

void assign_ng_to_g(){
  int i ;
  int *p ;
  int a[10];

  /*@ ghost
    int \ghost * gpg ;
    {
      gpg = &i ; // error: address of non-ghost integer into pointer to ghost
      gpg = p ;  // error: pointer to a non-ghost location into pointer to ghost
      gpg = a ;  // error: array of non-ghost values into pointer to ghost
    }
  */

  int (* nga) [10] ;
  //@ ghost int \ghost (*gpgagi)[10] ;
  //@ ghost gpgagi = nga ; // error: pointer to a non-ghost array into pointer to ghost array


  //@ ghost int \ghost * \ghost * p1 ;
  //@ ghost int        * \ghost * p2 ;
  //@ ghost int * array[10] ;

  //@ ghost p1 = p2 ;         // error: pointer to a pointer to non-ghost into pointer to pointer to ghost
  //@ ghost p1 = array ;      // error: array of pointers to non-ghost into pointer to pointer to ghost

  //@ ghost *p1 = *p2 ;       // error: pointer to non-ghost into pointer to ghost
  //@ ghost *p1 = array[0] ;  // error: pointer to non-ghost into pointer to ghost

  //@ ghost int \ghost * \ghost * \ghost * p3 ;
  //@ ghost int * \ghost (\ghost (*p4))[10] ;
  //@ ghost p3 = p4 ;         // error: pointer to ghost array of ghost pointers to non-ghost
                              //   into pointer to ghost pointers to ghost pointers to ghost

  struct Type ng_var ;
  //@ ghost int \ghost* r_ptr_2 ;
  //@ ghost r_ptr_2 = &(ng_var.field) ;     // error: address of a non-ghost field into pointer to ghost
}

void init_ng_to_g(void){
  int i ;
  int *p ;
  int a[10];

  //@ ghost int \ghost * gpg1 = &i ;  // error: address of non-ghost integer into pointer to ghost
  //@ ghost int \ghost * gpg2 = p ;   // error: pointer to a non-ghost location into pointer to ghost
  //@ ghost int \ghost * gpg3 = a ;   // error: array of non-ghost values into pointer to ghost

  //@ ghost int \ghost * gpg = function() ; // error: pointer to a non-ghost location into pointer to ghost

  int *p00, *p01 ;
  //@ ghost int \ghost * array[3] = { p00, p00, p01 };

  //@ ghost int_array ga ;
  //@ ghost int \ghost* ptr = ga ;
}

void call_ng_to_g(void){
  int i ;
  decl_ghost() /*@ ghost(&i) */ ; // error: address of non-ghost integer into pointer to ghost
  def_ghost() /*@ ghost(&i) */ ;  // error: address of non-ghost integer into pointer to ghost
}

//
// Ghost -> Non-ghost
//

//@ ghost int g ;
//@ ghost int \ghost * gl_gpg ;
//@ ghost int * gl_gp_1 = &g ;     // error: address of ghost integer into pointer to non-ghost
//@ ghost int * gl_gp_2 = gl_gpg ; // error: pointer to a ghost location into pointer to non-ghost


//@ ghost int \ghost *gl_pg00, *gl_pg01 ;
// error: we transform pointer to ghost into pointer to non-ghosts
//@ ghost int * gl_array_ng[3] = { gl_p00, gl_p00, gl_p01 };

void assign_g_to_ng(){
  //@ ghost int i ;
  //@ ghost int \ghost *p ;
  //@ ghost int a[10];

  /*@ ghost
    int * gp ;
    {
      gp = &i ; // error: address of ghost integer into pointer to non-ghost
      gp = p ;  // error: pointer to a ghost location into pointer to non-ghost
      gp = a ;  // error: array of ghost values into pointer to non-ghost
    }
  */

  //@ ghost int \ghost (*gpgagi) [10] ;
  //@ ghost int (*gpai)[10] ;
  //@ ghost gpgagi = gpai ; // error: pointer to a ghost array into pointer to non-ghost array


  //@ ghost int        * \ghost * p1 ;
  //@ ghost int \ghost * \ghost * p2 ;
  //@ ghost int \ghost * array[10] ;

  //@ ghost p1 = p2 ;         // error: pointer to a pointer to ghost into pointer to pointer to non-ghost
  //@ ghost p1 = array ;      // error: array of pointers to ghost into pointer to pointer to non-ghost

  //@ ghost *p1 = *p2 ;       // error: pointer to ghost into pointer to non-ghost
  //@ ghost *p1 = array[0] ;  // error: pointer to ghost into pointer to non-ghost

  //@ ghost int * \ghost * \ghost * p3 ;
  //@ ghost int \ghost * \ghost (\ghost (*p4))[10] ;
  //@ ghost p3 = p4 ;         // error: pointer to ghost array of ghost pointers to ghost
                              //   into pointer to ghost pointers to ghost pointers to non-ghost

  //@ ghost struct Type g_var ;

  //@ ghost int* r_ptr_3 ;
  //@ ghost r_ptr_3 = &(g_var.field) ; // error: address of a ghost field into pointer to non-ghost
}

/*@
  ghost
  /@ assigns \nothing ; @/
  int \ghost * function_g(void) ;
*/

void init_g_to_ng(void){
  //@ ghost int i ;
  //@ ghost int \ghost *p ;
  //@ ghost int a[10];

  //@ ghost int * gp1 = &i ;  // error: address of ghost integer into pointer to non-ghost
  //@ ghost int * gp2 = p ;   // error: pointer to a ghost location into pointer to non-ghost
  //@ ghost int * gp3 = a ;   // error: array of ghost values into pointer to non-ghost

  //@ ghost int * gpg = function_g() ; // error: pointer to a ghost location into pointer to non-ghost

  //@ ghost int \ghost *p00, *p01 ;
  //@ ghost int * array[3] = { p00, p00, p01 };

  //@ ghost int_array ga ;
  //@ ghost int * ptr = ga ;
}

void call_g_to_ng(void){
  //@ ghost int b = 42 ;
  decl_not_ghost() /*@ ghost(&b) */ ; // error: address of ghost integer into pointer to non-ghost
  def_not_ghost() /*@ ghost(&b) */ ;  // error: address of ghost integer into pointer to non-ghost
}

/*@ ghost
  /@ assigns \nothing ; @/
  void ghost_decl_nothing(int * a) ;

  void ghost_def_nothing(int * a){
    int x = *a ;
  }
*/

void ghost_calls(void){
  //@ ghost int g;
  //@ ghost ghost_decl_nothing(&g);
  //@ ghost ghost_def_nothing(&g);
}
