int x,y,*p;
main(){
  p = &x;
  while (p++ != &y);
}
