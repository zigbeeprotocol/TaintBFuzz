#define N 12

int t[12];

/*@ ensures 0 <= \result < N ; */
int get_index(void);

main()
{
  int i = get_index();
  t[i] = 3;
}
