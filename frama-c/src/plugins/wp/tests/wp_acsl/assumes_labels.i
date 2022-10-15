int v ;

/*@ assigns v ;
    behavior b1:
      assumes v == 1 ;
      ensures v == 2 ;
*/
void foo(void){
	if(v == 1) v = 2 ;
}

//@ requires v == 1 ;
void bar(void){
  foo();
  //@ check v == 2 ;
}
