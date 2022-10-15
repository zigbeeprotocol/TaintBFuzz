/* run.config
STDOPT: +"-dive-from-variables many_values::__retres,many_writes::x"
*/

int many_values(int x)
{
  int t1 = 0, t2 = 0, t3 = 0, t4 = 0, t5 = 0, t6 = 0, t7 = 0, t8 = 0, t9 = 0, t10 = 0, t11 = 0, t12 = 0, t13 = 0, t14 = 0;
  int *pt[14] = {
    &t1, &t2, &t3, &t4, &t5, &t6, &t7, &t8, &t9, &t10, &t11, &t12, &t13, &t14
  };
  
  if (x >= 0 && x < 14)
    return *pt[x];
  else
    return 0;
}

int many_writes()
{
  int t1 = 0, t2 = 0, t3 = 0, t4 = 0, t5 = 0, t6 = 0, t7 = 0, t8 = 0, t9 = 0, t10 = 0, t11 = 0, t12 = 0, t13 = 0, t14 = 0;

  int x = 0;
  x += t1;
  x += t2;
  x += t3;
  x += t4;
  x += t5;
  x += t6;
  x += t7;
  x += t8;
  x += t9;
  x += t1;
  x += t10;
  x += t11;
  x += t12;
  x += t13;
  x += t14;
  return x;
}

void main(int x)
{
  many_values(x);
  many_writes();
}
