/*@ axiomatic length {
  logic int string_length{L}(char* c);
  axiom no_string{L}: 
  \forall char* c; 
  (\forall integer j; 0<=j ==> c[j] != 0) ==>
  string_length(c) == -1;
  axiom has_length{L}:
  \forall char* c; \forall integer i; 0<=i ==>
  ((c[i] == 0 &&
    (\forall integer j; 0<=j<i ==> c[j]!=0))) <==> 
    string_length(c) == i;
}

predicate valid_string{L}(char* c) = string_length(c) >= 0 && 
        \valid(c+(0..string_length(c)));

lemma valid_string_not_zero{L}: 
\forall char* c; valid_string(c) ==> 
\forall integer j; 0<=j<string_length(c) ==>
  c[j] != 0;

lemma sublength{L}:
\forall char* c; valid_string(c) ==>
\forall integer i; 0<=i && (\forall integer j; 0<=j<=i ==> c[j]!=0) ==> 
i<string_length(c);

*/

/*@ requires valid_string(c);
  ensures \result == string_length(c);
  assigns \nothing;
*/
int str_len(char* c) {
  int i = 0;
  /*@ loop invariant \forall integer j; 0<=j<i ==> c[j] !=0;
      loop invariant 0<=i<=string_length(c);
      loop invariant c[i]!=0 ==> 0<=i<string_length(c);
   */
  while(c[i] !=0) i++;
  return i;
}

/*@ requires valid_string(src);
    requires \valid_range(dest,0,string_length(src));
    ensures valid_string(dest);
    ensures \forall integer i; 0<=i<=string_length(src) ==> src[i] == dest[i];
    assigns dest[0..string_length{Post}(src)];
 */
void str_cpy(char* src, char* dest) {
  int i = 0;
  /*@ loop invariant 0<=i<=string_length(src);
      loop invariant \forall integer j; 0<=j<i ==> dest[j] == src[j];
      loop invariant \forall integer j; 0<=j<i ==> src[j] !=0;
      loop invariant src[i]!=0 ==> i<string_length(src);
      loop assigns dest[0..i-1];
  */
  while (src[i]) {dest[i]=src[i]; i++;}
  /*@ assert i == string_length(src); */
  dest[i] = src[i];
  /*@ assert i == string_length(dest); */
}

/*
Local Variables:
compile-command: "frama-c -jessie string.c"
End:
*/
