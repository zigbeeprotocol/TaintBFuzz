/*@ exits \false;
  @ assigns *(message + (0 .. \at(*\old(size),Post) - 1)), *size;
*/
void receive1(unsigned char *message, unsigned int *size);

/*@ exits \false;
  @ assigns *(message + (0 .. \at(*\old(size),Post) - 1)), *size;
*/
void mess1(unsigned char *message, unsigned int *size) {
   receive1(message, size);
}
