/* run.config
 MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

void declaration_void(void) /*@ ghost (int x, int y) */ ;
void declaration_not_void(int a, int b) /*@ ghost (int x, int y) */ ;

void definition_void(void) /*@ ghost(int x, int y) */ {

}

void definition_not_void(int a, int b) /*@ ghost(int x, int y) */ {

}

void caller(){
  declaration_void() /*@ ghost (1, 2) */ ;
  declaration_not_void(1, 2) /*@ ghost (3, 4) */ ;
  definition_void() /*@ ghost (1, 2) */ ;
  definition_not_void(1, 2) /*@ ghost (3, 4) */ ;
}
