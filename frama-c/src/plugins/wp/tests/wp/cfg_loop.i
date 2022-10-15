/* -------------------------------------------------------------------------- */
/* --- Bugs related to CFG for loops & switch                             --- */
/* -------------------------------------------------------------------------- */

// All contract shall be provable

void loop_switch(int *a,int c)
{
  *a = 1;
  int b = 2;
  /*@
    loop invariant b == 2;
    loop invariant *a ==1;
    loop assigns b, *a;
  */
  while(1) {
    switch (c) {
    case 1:
      *a = 1;
      b = 2;
      break;
    case 2:
      b = 2;
      *a = 1;
      break;
    default:
      *a =1;
      b = 2;
      break;
    }
  }
}

int a;

void loop_continue(int x,int y)
{
  int *p = &a;
  /*@
    loop invariant p == \at(p, LoopEntry);
    loop assigns *p, x;
  */
  while(1)
    {
      if(x)
        {
          if (y)
            continue;
          *p = 1;
          x++;
        }
      else
        return;
    }
}
