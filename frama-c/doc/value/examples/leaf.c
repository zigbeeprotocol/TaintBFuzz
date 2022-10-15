
int g_int(void);

int *g_ptr(void);

int **g_ptrptr(void);


int X, *Y, **Z;

void main(void)
{
  X = g_int();
  Y = g_ptr();
  Z = g_ptrptr();
  // **Z = 3;
  *Z = Y;
}
   
  
