void f(int a __attribute__((unused)) );

int main(void){
  void (*op) (int) = f ;
  //@ assert op == f ;
}
