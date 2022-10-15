/* run.config
   STDOPT: #" -warn-unsigned-overflow -print -machdep x86_32"
   STDOPT: #" -warn-unsigned-overflow -print -machdep x86_64"
*/
unsigned long f(unsigned int n)
{
  return n * sizeof(unsigned long);
}
