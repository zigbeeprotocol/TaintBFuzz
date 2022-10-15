/* run.config
 EXIT: 1
   OPT:-cpp-extra-args="-DFAIL_DECL_TYPE"
 EXIT: 0
 MODULE: @PTEST_NAME@
   OPT:
*/


/* When there is no comment, the code should be allowed */
void f_ints(){
  int ng ;

  //@ ghost int g0 ;
  //@ ghost int \ghost g1 ;     // should warn (g1 is already ghost)
}

void f_ptrs(){
  int* ng ;

  /*@ ghost
    int * g ;
    int \ghost* g0 ;

    int * \ghost g1 ;           // should warn (g1 is already ghost)
    int \ghost * \ghost g2 ;    // should warn (g2 is already ghost)
  */
}

void f_arrays(){
  int ng[10] ;

  /*@ ghost
    int g[10] ;
    int \ghost g0[10] ;         // should warn (g0 elements are already ghost)
  */
}

struct S {
  int field ;
};

void f_structs(void){
  struct S ng ;

  /*@ ghost
    struct S g ;
    struct S \ghost g0 ;         // should warn (g0 is already ghost)
  */
}

typedef int int_array [10] ;
typedef int* int_ptr ;

void named(void){
  //@ ghost int_array a ;
  //@ ghost int_ptr ptr ;
}

struct S_with_pointer {
  int * field ;
};

struct S_with_array {
  int field[10] ;
};

struct S_with_ptr_of_array {
  int (*field) [10] ;
};

struct S_with_array_of_ptr {
  int* field [10] ;
};

void nesting_non_ghost (void){
  int a ;
  int * ptr ;
  int array[10] ;

  int * * pptr ;
  int (* parray)[10] ;
  int * aptr[10] ;
  int aarray[10][10] ;

  struct S_with_pointer sp ;
  struct S_with_array sa ;
  struct S_with_ptr_of_array spa ;
  struct S_with_array_of_ptr sap ;

  struct S_with_pointer * psp ;
  struct S_with_array * psa ;
  struct S_with_ptr_of_array * pspa ;
  struct S_with_array_of_ptr * psap ;

  struct S_with_pointer asp[10] ;
  struct S_with_array asa[10] ;
  struct S_with_ptr_of_array aspa[10] ;
  struct S_with_array_of_ptr asap[10] ;

  a = 1 ;
}

void nesting_ghost(void){
  /*@ ghost {
      int a ;
      int * ptr ;
      int \ghost * ptrg ;

      int array[10] ;

      int * * pptr ;
      int * \ghost * pptrg ;
      int \ghost * \ghost * pptrgg ;

      int (* parray)[10] ;
      int \ghost (* parrayg)[10] ;

      int * aptr[10] ;
      int \ghost * aptrg[10] ;

      int aarray[10][10] ;

      struct S_with_pointer sp ;
      struct S_with_array sa ;
      struct S_with_ptr_of_array spa ;
      struct S_with_array_of_ptr sap ;

      struct S_with_pointer * psp ;
      struct S_with_pointer \ghost * pspg ;

      struct S_with_array * psa ;
      struct S_with_array \ghost * psag ;

      struct S_with_ptr_of_array * pspa ;
      struct S_with_ptr_of_array \ghost * pspag ;

      struct S_with_array_of_ptr * psap ;
      struct S_with_array_of_ptr \ghost * psapg ;

      struct S_with_pointer asp[10] ;
      struct S_with_array asa[10] ;
      struct S_with_ptr_of_array aspa[10] ;
      struct S_with_array_of_ptr asap[10] ;

      a = 1 ;
    }
  */
}
#ifdef FAIL_DECL_TYPE /* In this section types are ill-formed (ghost -> non-ghost -> ghost) */
/*@ ghost
  int \ghost * * decl_bad_return_type(void) ;
  void decl_bad_parameter_type(int \ghost * * param) ;
  int \ghost * * def_bad_return_type(void) {
    return 0 ;
  }
  void def_bad_parameter_type(int \ghost * * param) {
  }
  void reference_bad_types_functions (void) {
    decl_bad_return_type() ;
    decl_bad_parameter_type(0) ;
  }
*/
void ghost_incorrect(void){
  /*@ ghost {
      int \ghost * * pptrg ;

      pptrg = 0 ;
    }
  */
}
#endif

void foo_1(int a){

}

void foo_2(int a) /*@ ghost (int \ghost b) */ { // should warn (b is already ghost)

}

void foo_3(int a) /*@ ghost (int b, int c) */ {

}

void bar_1(int a) ;
void bar_2(int a) /*@ ghost (int \ghost b) */ ; // should warn (b is already ghost)
void bar_3(int a) /*@ ghost (int b, int c) */ ;

void pfoo_1(int* a){

}

void pfoo_2(int a) /*@ ghost (int * \ghost b) */ { // should warn (b is already ghost)

}

void pfoo_3(int a) /*@ ghost (int \ghost* b, int * c) */ {

}

void pbar_1(int* a) ;
void pbar_2(int a) /*@ ghost (int * \ghost b) */ ; // should warn (b is already ghost)
void pbar_3(int a) /*@ ghost (int \ghost* b, int * c) */ ;

void afoo_1(int a[10]){

}

void afoo_2(int a) /*@ ghost (int \ghost b[10]) */ { // should warn (b elements are already ghost)

}

void afoo_3(int a) /*@ ghost (int b[10]) */ {

}

void abar_1(int a[10]) ;
void abar_2(int a) /*@ ghost (int \ghost b[10]) */ ; // should warn (b elements are already ghost)
void abar_3(int a) /*@ ghost (int b[10]) */ ;


void reference_functions(){
  bar_1(1);
  bar_2(1) /*@ ghost (1) */;
  bar_3(1) /*@ ghost (1, 1) */;

  int v ;
  //@ ghost int \ghost* gp ;
  pbar_1(&v);
  pbar_2(1) /*@ ghost (&v) */;
  pbar_3(1) /*@ ghost (gp, &v) */;

  int ng[10] ;
  //@ ghost int ga[10] ;
  abar_1(ng);
  abar_2(1) /*@ ghost (ga) */;
  abar_3(1) /*@ ghost (ga) */;
}

//@ ghost int x ;
int i ;
int * p ;

//@ ghost int * gp1 = &i ;
//@ ghost int * gp2 = p ;

//@ ghost int x = 42 ;

int main(){
  //@ ghost int value = x + *gp1 + *gp2 ;
}
