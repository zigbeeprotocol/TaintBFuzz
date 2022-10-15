/*@ assigns \nothing;
  @ behavior even:
  @   assumes m % 2 == 0;
  @   ensures \result >= 1;
  @ behavior odd:
  @   assumes m % 2 != 0;
  @   ensures n >= 0 ==> \result >= 1; 
  @   ensures n < 0 ==> \result <= -1; */
int pow(int n, unsigned int m);

int sum(int x) {
  int n = 0, i;
  for(i = 1; i <= x; i++) n += i;
  return n;
}

int main(void) {
  int i, n = 0;
  unsigned int a[100];
  n = sum(10);
  /*@ loop invariant 0 <= i <= n ;
    @ loop invariant \forall integer k; 0 <= k < i ==> a[k] >= 1;
    @ loop assigns i,a[0..n-1]; */
  for(i = 0; i < n; i++) {
    int tmp = pow(i, i);
    a[i] = tmp;
  }
  /*@ assert \forall integer k; 0 <= k < n ==> a[k] >= 1; */
}
