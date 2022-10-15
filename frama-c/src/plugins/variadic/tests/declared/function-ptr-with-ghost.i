void function(void (*p) (int, ...) /*@ ghost (int v) */, int x){
  (*p) (x, 1, 2, 3) /*@ ghost (4) */;
}
void va_f(int, ...) /*@ ghost(int x) */ ;

int main(void){
  function(va_f, 3);
}
