void l_int(void){
  int x = 1 ;
  //@ assert SUCCS: x == 1;
  //@ assert SUCCS: \initialized(&x);
  //@ check FAILS: \false ;
}
void l_array(void){
  int x[3] = { 0 } ;
  //@ assert SUCCS: x[0] == x[1] == x[2] == 0 ;
  //@ assert SUCCS: \initialized(&x);
  //@ check FAILS: \false ;
}
typedef struct { int x ; char t[2] ; } S;
void l_struct(void){
  S s = { 0 };
  //@ assert SUCCS: s.x == s.t[0] == s.t[1] == 0 ;
  //@ assert SUCCS: \initialized(&s);
  //@ check FAILS: \false ;
}
