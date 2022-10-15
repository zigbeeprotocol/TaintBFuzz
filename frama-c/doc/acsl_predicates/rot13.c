
/*@  predicate string_of_length{L}(unsigned char *s, integer n) =
   n >= 0 &&
   \valid_range(s, 0, n) &&
   s[n] == 0 &&
   \forall integer k ; (0 <= k < n) ==> (s[k] != 0) ;

   lemma always_the_same_length{L}:
   \forall unsigned char *s, integer n1, integer n2 ;
      (string_of_length(s, n1) && string_of_length(s, n2)) ==> n1 == n2 ;
*/

/*@ axiomatic Length
  {
    logic integer length{L}(unsigned char *s) reads s[..] ;    
    axiom string_length{L}:
      \forall integer n, unsigned char *s ;
        string_of_length(s, n) ==> length(s) == n ;
  }
*/

/*@
  assigns \nothing ;
*/
unsigned char rot13_char(unsigned char c)
{
  if ((c >= 'a' && c <= 'm') || (c >= 'A' && c <= 'M')) return c + 13;
  if ((c >= 'n' && c <= 'z') || (c >= 'N' && c <= 'Z')) return c - 13;
  return c;
}

/*@ 
  requires \exists integer n ; 0 <= n <= 2000000000 && string_of_length(s,n) ;
  assigns s[..] ;
//  ensures is_rot13{Pre,Post}(s,s) ;
 */
void rot13(unsigned char *s)
{
  int i;
  /*@ 
    loop assigns i, s[..];
    loop invariant s[length{Pre}(s)]==0 ;
    loop invariant 0 <= i <= length{Pre}(s) ;
    loop variant length(s) - i ;
   */
  for(i=0; s[i]; ++i)
    {
      s[i] = rot13_char(s[i]);
    }
}
