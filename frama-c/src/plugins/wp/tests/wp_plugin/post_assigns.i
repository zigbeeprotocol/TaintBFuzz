/*@
  assigns *(message + (0 .. n));
*/
extern void write(char *message, int n);

int size;

/*@
  ensures size == n;
  assigns size, message[ 0 .. \at(size,Post) ];
*/
void receive(int n,char *message) {
  size = n ;
  write(message, size);
}
