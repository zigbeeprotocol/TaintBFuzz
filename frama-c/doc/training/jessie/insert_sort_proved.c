/*@
  axiomatic Nb_occ {
    logic integer nb_occ{L}(int* arr, integer low, integer high, int val);
    axiom nb_occ_0{L}: \forall int* arr, integer low, high, int val;
    high < low ==> nb_occ(arr,low,high,val) == 0;

    axiom nb_occ_eq{L}: \forall integer low,high, int* arr,int v;
    v == arr[high] ==>
    nb_occ(arr,low,high,v) == nb_occ(arr,low,high-1,v)+1;

    axiom nb_occ_neq{L}: \forall integer low,high,int* arr,int v;
    v!=arr[high] ==>
    nb_occ(arr,low,high,v) == nb_occ(arr,low,high-1,v);

  }
*/

/*@
    lemma nb_occ_split{L}: \forall int* arr, integer low,med,high, int val;
      low<=med<=high ==>
      (nb_occ(arr,low,high,val) ==
       nb_occ(arr,low,med, val) + nb_occ(arr,med+1,high,val));

    lemma nb_occ_same{L1,L2}:
     \forall integer low1,high1,low2,high2,int* arr,int v;
      high1 - low1 == high2 - low2 ==>
      (\forall integer i; 0<=i<=high1-low1 ==>
      \at(arr[low1+i],L1) == \at(arr[low2+i],L2)) ==>
      nb_occ{L1}(arr,low1,high1,v) == nb_occ{L2}(arr,low2,high2,v);

      lemma nb_occ_rev{L}: \forall int* arr, integer low, high, int val;
      low<=high ==>
      ((arr[low] == val ==>
           nb_occ(arr,low,high,val) == nb_occ(arr,low+1,high,val)+1) &&
       (arr[low] != val ==>
           nb_occ(arr,low,high,val) == nb_occ(arr,low+1,high,val)));
*/

/*@ predicate sorted{L}(int* arr, integer length) =
  \forall integer i; 0<=i<length-1 ==> arr[i] <= arr[i+1];
*/

/*@ requires \valid_range(arr,0,length);
    requires length >=0;
    requires sorted(arr,length);
    assigns arr[0..length];
    ensures sorted(arr,length+1);
    ensures \forall int v;
    (v!=val ==>
      nb_occ(arr,0,length,v) == nb_occ{Old}(arr,0,length-1,v)) &&
    (v ==val ==>  nb_occ(arr,0,length,v) == nb_occ{Old}(arr,0,length-1,v) + 1);
*/
void insert(int* arr, int length, int val);

/*@ requires \valid_range(arr,0,length-1);
  requires length >=0;
  assigns arr[0..length-1];
  ensures sorted(arr,length);
  ensures \forall int v; nb_occ(arr,0,length-1,v) ==
            nb_occ{Old}(arr,0,length-1,v);
 */
void insert_sort(int* arr, int length);

void insert(int* arr, int length, int val) {
  int i = length -1;
  /*@
    loop invariant -1<=i<length;
      loop invariant \forall integer j;
        0<=j<=i+1 ==> arr[j] == \at(arr[j],Pre);
      loop invariant \forall integer j;
            i+1<j<=length ==> arr[j]==\at(arr[j-1],Pre);
      loop invariant \forall integer j;
            i+1<j<=length ==> arr[j] > val;
      loop invariant \forall int v;
        nb_occ(arr,0,i,v) == nb_occ{Pre}(arr,0,i,v);
      loop invariant \forall int v;
        nb_occ(arr,i+2,length,v) ==
         nb_occ{Pre}(arr,i+1,length-1,v);
      //loop invariant sorted(arr,length) && i < length - 1 ==> sorted(arr,length+1);
   */
  while(i>=0 && arr[i] > val) { arr[i+1] = arr[i]; i--; }
  arr[i+1] = val;
  return;
}

void insert_sort(int* arr, int length)  {
  if (length > 0) {
  /*@
    loop invariant 1<=i<=length;
    loop invariant sorted(arr,i);
    loop invariant \forall integer j; i<j<length ==> arr[j]==\at(arr[j],Pre);
    loop invariant \forall int v;
    nb_occ(arr,0,length-1,v) == nb_occ{Pre}(arr,0,length-1,v);
  */
      for(int i = 1; i < length; i++) { insert(arr,i,arr[i]); }}
}

//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie insert_sort.c"
End:
*/
//NOPP-END
