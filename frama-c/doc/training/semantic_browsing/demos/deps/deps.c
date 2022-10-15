
int Xs, Z;

const int I_size = 8;
const int Itab[8] = {-40, -25, -15, -5, 5, 15, 25, 40 };

int main(int i1, int es, int i2) {
  int a;
  es = i1 ;
  Xs = es ;
  if (i2 < Itab[0])
    a = -2;
  else if (i2 >= Itab[I_size-1])
    a = -1;
  else
    for(Z = 0; Z < I_size - 1; Z++)
      if (i2 >= Itab[Z] && i2 < Itab[Z+1])
	a = Z;
  return a;
}
