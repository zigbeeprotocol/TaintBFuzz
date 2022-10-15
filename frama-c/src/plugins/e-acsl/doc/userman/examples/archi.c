#define ARCH_BITS 64 /* assume a 64-bit architecture */

#if ARCH_BITS == 32
#define SIZEOF_LONG 4
#elif ARCH_BITS == 64
#define SIZEOF_LONG 8
#endif

int main(void) {
  /*@ assert sizeof(long) == SIZEOF_LONG; */
  return 0;
}
