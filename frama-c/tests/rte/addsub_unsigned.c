/* run.config
   STDOPT: #" -warn-signed-overflow -print -machdep x86_32"
   STDOPT: #" -warn-signed-overflow -warn-unsigned-overflow -print -machdep x86_32 "
*/

int main() {
  
  unsigned int ux,uy,uz;

  ux = 0x7FFFFFFFU * 2 ; /* no unsigned ov */

  uy = 0x80000000U +  0x80000000U; /* unsigned ov */

  uy = 2U * 0x80000000U; /* unsigned ov */

  uz = ux + 2; /* unsigned ov but not detected by const folding */

  return 0;
}
