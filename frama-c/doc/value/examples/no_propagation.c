int x, y, z;
main(int c){
  x = c ? 0 : 1;
  y = x ? 0 : 1;
/* At this point the value analysis guarantees:
   x IN {0; 1} 
   y IN {0; 1}; */
  z = 10 / (x - y);
}
