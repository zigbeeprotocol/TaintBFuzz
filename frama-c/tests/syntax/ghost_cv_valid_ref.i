// This file should be entirely accepted

struct Type {
  int field ;
} ;

void decl_ghost(void) /*@ ghost (int \ghost * p) */ ;

void def_ghost(void) /*@ ghost (int \ghost * p) */ {

}

void decl_not_ghost(void) /*@ ghost (int * p) */ ;

void def_not_ghost(void) /*@ ghost (int * p) */ {

}

int main(){
  int i ;
  int *p ;
  int a[10];

  //@ ghost int * gp1 = &i ;
  //@ ghost int * gp2 = p ;
  //@ ghost int * gp3 = a ;

  /*@
    ghost {
      gp1 = &i ;
      gp2 = p ;
      gp3 = a ;
    }
  */

  struct Type ng_var ;
  //@ ghost struct Type g_var ;


  int* a_ptr_1 = &(ng_var.field) ;
  //@ ghost int* a_ptr_2 = &(ng_var.field) ;

  //@ ghost int \ghost* a_ptr_4 = &(g_var.field) ;

  //@ ghost int b = 42 ;

  decl_ghost() /*@ ghost(&b) */ ;
  def_ghost() /*@ ghost(&b) */ ;

  decl_not_ghost() /*@ ghost(&i) */ ;
  def_not_ghost() /*@ ghost(&i) */ ;
}
