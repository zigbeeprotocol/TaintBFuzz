// handling recursive functions (implicit call to __e_acsl_rec_id)

/*@ ensures x >= 0 ==> \result == x; */
int rec_id(int x) {
  int tmp;
  if (x <= 0) return 0;
  return 1 + rec_id(x - 1);
}

int main(void) {
  int x = rec_id(4);
  return 0;
}
