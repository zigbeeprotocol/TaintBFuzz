/* run.config*
   
   STDOPT: #"-absolute-valid-range 0-0x3"
*/

int * f() {
  return 100;
}

void crash () {
  unsigned int v = 1;
  *((f()))=v;
}


char R;
void main(int c) {
  if(c) crash();

  *((char*)0)=2;
  R = *((char*)1);
  *((char*)2)=2;
  R = *((char*)3);
}
