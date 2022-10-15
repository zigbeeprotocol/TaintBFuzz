/*@
  requires \valid( p + (0..n-1) );
  assigns p[0..n-1];
 */
void job(int *p,int n);

struct S {
  int size ;
  int value[50] ;
} s ;

/*@
  requires s.size < 50;
  assigns s.value[1..s.size];
*/
void complex(void)
{
  job( & s.value[1] , s.size );
}
