/* run.config
 EXIT: 1
   OPT:-no-autoload-plugins -cpp-extra-args="-DCAN_CHECK"
   OPT:-no-autoload-plugins -cpp-extra-args="-DCANT_CHECK"
*/

#ifdef CAN_CHECK

int first_stmt(void){
  //@ ghost goto X ;   // breaks CFG by reaching "return 1" instead of "return 0"
  return 0 ;
  //@ ghost X: ;
  return 1 ;
}

void break_allowed(){ // OK
  /*@ ghost
    for(int i = 0 ; ; ++i){
      if(i == 10) break ;
    }
  */
}

void break_refuse(){
  int i = 0;
  while(i < 10){
    //@ ghost if(i == 0) break ; // by-passes loop body
    i++;
  }
}

void continue_refuse(){
  int i = 0;
  while(i < 10){
    //@ ghost if(i == 0) continue ; // by-passes loop body
    i++;
  }
}

void if_construct(int x){ // OK
  //@ ghost int c ;

  x ++ ;
  /*@ ghost
    if (x == 0){
      c = 1 ;
    }
    else {
      c = 2 ;
    }
  */
  x ++ ;
}

void switch_construct(){
  int i = 42 ;
  int x = 0 ;
  //@ ghost int g ;
  switch(i){
  case 0: x = 3 ; break ;
    { /*@ ghost case 1: g = 3 ;*/ }             // case 1 instead of going to default goes to case 2
  case 2: /*@ ghost g = 5 ;*/ i = 101 ; break ;
  /*@ ghost case 3: g = 6 ; break ;*/
  }
}

void block_with_assert(){ // OK
  int x = 1 ;

  {
    //@ assert x == 1 ;
  }

  x = 2 ;
}

int ghost_goto_non_ghost(){
  int x = 3 ;

  //@ ghost goto X ; // reaches return without executing "x = 2"
  x = 2;

 X:
  return 0;
}

int ghost_goto_ghost(){
  int x = 3 ;

  //@ ghost goto X ; // reaches return without executing "x = 2"
  x = 2;

  //@ ghost X:;
  return 0;
}

void switch_loses_assertion (int c) {
  //@ ghost int x = 1;
  switch (c) {
    case 0: return;
    //@ ghost case 1: x++; /*@ assert x == 2; */ break;
    default: /*@ assert x == 1; */ break;
  }
  return;
}

int ghost_return() {
  // the following ghost statement makes the function returning 1 instead of 0
  //@ ghost return 1;
  return 0;
}

void shared_cfgs(int x) {
  switch (x) {
    /*@ ghost case 3: ; */
  case 2: ;
    x = 5;
  default: ;
    x ++;
  }
}

void ghost_else(int x) /*@ ghost(int y) */ {
  if(x){
    x++;
  } /*@ ghost else {
    y++;
  } */

  if(x){
    goto X ;
  } /*@ ghost else {
    goto X ; // breaks CFG
  } */

  x++;
 X:
  x++;

  if(x){
    x++;
  } /*@ ghost else {
    return; // breaks CFG
  } */

  x++;
}

#endif

#ifdef CANT_CHECK

int main(){
  goto X ; // This non-ghost goto cannot see the label "X" as it is ghost

  int x = 4 ;

  //@ ghost X:;

  x = 2 ;
}

#endif
