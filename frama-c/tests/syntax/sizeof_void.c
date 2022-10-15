/* run.config
   EXIT: 1
   STDOPT: +"-machdep x86_64"
   EXIT: 0
   STDOPT: +"-machdep gcc_x86_64"
*/

int f () {
  int x = sizeof(void);
  return 0;
}

int g () {
  void *p;
  int x = sizeof(p);
  int y = sizeof(*p);
  return 0;
}

int h () {
  int x = __alignof__(void);
  return 0;
}

int i () {
  void *p;
  int x = __alignof__(p);
  int y = __alignof__(*p);
  return 0;
}
