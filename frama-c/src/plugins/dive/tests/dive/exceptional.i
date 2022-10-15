/* run.config
STDOPT: #"-machdep x86_32" +"-absolute-valid-range 0x10000000-0x1fffffff -dive-from-variables main::__retres -dive-depth-limit 5"
*/

int* gm(int *p) { return (int *) ((unsigned int) p * 2 / 2); }


int main(void)
{
  // String
  char *s = "lorem ipsum";
  char c = s[4];

  // Unknown
  int i;
  int *p = gm(&i);
  int x = *p;

  // Absolute
  int *r = 0x10000000;
  int a = *r;

  return a + x + c;
}
