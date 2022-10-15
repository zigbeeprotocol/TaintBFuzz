/*@ ensures (\result == -\at(x,Old));
    behavior pos:
      assumes (x >= 0);
      ensures (\result <= 0);
      assigns *y;
    behavior neg:
      assumes (x < 0);
      ensures (\result > 0);
      assigns \nothing; 
*/
int f(int x , int *y ) 
{
  int __retres ;
  if (x >= 0) { *y = x; }
  __retres = - x;
  return (__retres);
}
