/* run.config
   STDOPT: +"-print "
   STDOPT: +"-main nop1 -slice-pragma nop1 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop2 -slice-pragma nop2 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop3 -slice-pragma nop3 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop4 -slice-pragma nop4 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop5 -slice-pragma nop5 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop6 -slice-pragma nop6 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop7 -slice-pragma nop7 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main nop8 -slice-pragma nop8 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main double_effect1 -slice-pragma double_effect1 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main double_effect2 -slice-pragma double_effect2 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main double_effect3 -slice-pragma double_effect3 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main double_effect4 -slice-pragma double_effect4 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main double_effect5 -slice-pragma double_effect5 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test1 -slice-pragma test1 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test2 -slice-pragma test2 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test3 -slice-pragma test3 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test4 -slice-pragma test4 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test5 -slice-pragma test5 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test6 -slice-pragma test6 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test7 -slice-pragma test7 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test8 -slice-pragma test8 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-main test9 -slice-pragma test9 -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
*/
typedef int stmt, expr, slice;
int x, y ;
//-------------------
void nop1(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing isn't correct since the effect...
  ; // <----- ...is missing with -print option
  x = 1 ;
 }
void nop2(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing isn't correct since the effect...
  {;} // <----- ...is missing with -print option
  x = 1 ;
 }

void nop3(int c1, int c2) {
  //@ slice pragma stmt;  // <----- slicing isn't correct since the effect...
  {;{;;};} // <----- ...is missing with -print option
  x = 1 ;
 }
void nop4(int c1, int c2) {
  //@ slice pragma stmt;
  if (c1) {;{;;};}
  x = 1 ;
 }
void nop5(int c1, int c2) {
  if (c2) goto L ;
  //@ slice pragma stmt; // <----- slicing is correct, but not the output
 L:;
  x = 1 ;
 }
void nop6(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing is correct, but not the output
 L:;
  x = 1 ;
 }
void nop7(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing is correct, but not the output
 L:{;}
  x = 1 ;
 }
void nop8(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing is correct, but not the output
  {L:{;}}
  x = 1 ;
 }
//-------------------
void double_effect1(int c1, int c2) {
  //@ slice pragma stmt;  // <----- slicing isn't correct since the...
  x += y++ ;   // <----- ...effect is lost with -print option
 }
void double_effect2(int c1, int c2) {
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
  { x += y++ ; }   // <----- ...effect is lost with -print option
 }
void double_effect3(int c1, int c2) {
  if (c2) goto L ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
  L: x += y++ ;   // <----- ...effect is lost with -print option
 }
void double_effect4(int c1, int c2) {
  if (c2) goto L ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
 L: {x += y++ ; }   // <----- ...effect is lost with -print option
 }
void double_effect5(int c1, int c2) {
  if (c2)
    //@ slice pragma stmt;
    {x += y++ ; }
 }
//-------------------
void test1(int c1, int c2) {
  if (c1 < c2)
    c1 = c2 ;
  //@ slice pragma stmt;
  x = c1 ;
}
void test2(int c1, int c2) {
  if (c1 < c2)
    c1 = c2 ;
  //@ slice pragma stmt;
  x = c1 ;
  y = c2 ;
}
void test3(int c1, int c2) {
  if (c1 < c2)
    c1 = c2 ;
  //@ slice pragma stmt;
  {x = c1 ;}
  y = c2 ;
}
void test4(int c1, int c2) {
  if (c1 < c2)
    c1 = c2 ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
  {x = c1 ; c2 ++ ;}  // <----- ...effect is lost with -print option
  y = c2 ;
}
void test5(int c1, int c2) {
  if (c1 < c2)
    goto L;
  c1 = c2 ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
 L: x = c1 ;   // <----- ...effect is lost with -print option
  y = c2 ;
}
void test6(int c1, int c2) {
  if (c1 < c2)
    goto L;
  c1 = c2 ;
  //@ slice pragma stmt;  // <----- slicing isn't correct since the...
 L: x = c1++ ;   // <----- ...effect is lost with -print option
  y = c2 ;
}
void test7(int c1, int c2) {
  if (c1 < c2)
    goto L;
  c1 = c2 ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
 L: {x = c1++ ; c2 ++ ;}   // <----- ...effect is lost with -print option
  y = c2 ;
}
void test8(int c1, int c2) {
  if (c1 < c2)
    goto L;
  c1 = c2 ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
  { L: x = c1++ ; c2 ++ ;}   // <----- ...effect is lost with -print option
  y = c2 ;
}
void test9(int c1, int c2) {
  if (c1 < c2)
    goto L;
  c1 = c2 ;
  //@ slice pragma stmt; // <----- slicing isn't correct since the...
  { x = c1 ; L: c2 = c2 + 1 ;}   // <----- ...effect is lost with -print option
  y = c2 ;
}
