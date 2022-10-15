/* run.config
MODULE: @PTEST_NAME@
  OPT: -print
*/


int main(){
  int i = 0 ;
  //@ ghost int j = 0 ;

  i++ ;
  //@ ghost j++ ;

  {
    //@ ghost int x = 0;
    //@ ghost x++ ;
  }
}
