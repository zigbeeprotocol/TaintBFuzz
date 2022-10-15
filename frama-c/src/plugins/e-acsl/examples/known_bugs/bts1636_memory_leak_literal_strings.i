int main(void)
{
  char *s;
  for(int i = 0; i < 10; i++) {
    s = "012";
  }
  /*@ assert s[1] == '1'; */
  return 0;
}
