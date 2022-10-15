int a ;

/*@
  requires a == 1;
  ensures a == 1;
*/
void LoopCurrent()
{
  /*@
    loop assigns s,a;
    loop invariant A: \at(a, LoopCurrent)== 1;
    loop variant 10-s;
  */
  for(int s = 0; s< 10; s++)
    {
      a = 2;
    }
}
