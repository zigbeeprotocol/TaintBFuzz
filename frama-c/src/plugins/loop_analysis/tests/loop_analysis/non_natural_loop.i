void duff(int *to, int *from, int count) {
  register n = (count + 7) / 8;
  switch(count % 8) {
  case 0: do {
      Frama_C_show_each(to);
      *to++ = *from++;
    case 7:   *to++ = *from++;
    case 6:   *to++ = *from++;
    case 5:   *to++ = *from++;
    case 4:   *to++ = *from++;
    case 3:   *to++ = *from++;
    case 2:   *to++ = *from++;
    case 1:   *to++ = *from++;
    } while(--n > 0);
  }
}

int f() {
  int i = 3;
  return i;
  // dead loop
  for (i = 0; i < 5; i++)
    i = i+1;
}
