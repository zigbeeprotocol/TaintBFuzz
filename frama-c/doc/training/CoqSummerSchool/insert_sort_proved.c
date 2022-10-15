/* Définition axiomatique du nombre d'occurence de val dans un bloc mémoire. */
/*@
  axiomatic Nb_occ {
    logic integer nb_occ{L}(int* arr, integer low, integer high, integer val);
    axiom nb_occ_0{L}: \forall int* arr, integer low, high, integer val;
    high < low ==> nb_occ(arr,low,high,val) == 0;

    axiom nb_occ_eq{L}: \forall integer low,high, int* arr,integer v;
    low <= high && v == arr[high] ==>
    nb_occ(arr,low,high,v) == nb_occ(arr,low,high-1,v)+1;

    axiom nb_occ_neq{L}: \forall integer low,high,int* arr,integer v;
    low <= high && v!=arr[high] ==>
    nb_occ(arr,low,high,v) == nb_occ(arr,low,high-1,v);

  }
*/

/* Quelques lemmes auxiliaires sur nb_occ. Ils se prouvent par induction sur la
   taille du bloc, ce qui n'est pas très accessible aux prouveurs.
*/
/*@
  lemma nb_occ_split{L}: \forall int* arr, integer low,med,high, integer v;
      low <= med < high ==> nb_occ(arr,low,high,v) ==
       nb_occ(arr,low,med,v)+nb_occ(arr,med+1,high,v);

    lemma nb_occ_split_1{L}:
       \forall int* arr, integer low,med,high, integer val;
      low <= med <= high &&
      arr[med] == val ==>
      (nb_occ(arr,low,high,val) ==
       nb_occ(arr,low,med-1,val) + nb_occ(arr,med+1,high,val)+1);

    lemma nb_occ_split_2{L}:
      \forall int* arr, integer low,med,high, integer val;
      low <= med <= high &&
      arr[med] != val ==>
      (nb_occ(arr,low,high,val) ==
       nb_occ(arr,low,med-1,val) + nb_occ(arr,med+1,high,val));

    lemma nb_occ_same{L1,L2}:
     \forall integer low1,low2,high1,high2,int* arr,integer v;
     high1 - low1 == high2 - low2 &&
      (\forall integer i; 0<=i<= high1 - low1 ==>
      \at(arr[low1+i],L1) == \at(arr[low2+i],L2)) ==>
      nb_occ{L1}(arr,low1,high1,v) ==
      nb_occ{L2}(arr,low2,high2,v);

    lemma nb_occ_same_2{L1,L2}:
     \forall integer low1,high1,int* arr,integer v;
      (\forall integer i; low1<=i<= high1 ==>
      \at(arr[i],L1) == \at(arr[i],L2)) ==>
      nb_occ{L1}(arr,low1,high1,v) ==
      nb_occ{L2}(arr,low1,high1,v);

*/

/* Predicat de tri */

/*@ predicate sorted{L}(int* arr, integer length) =
  \forall integer i; 0<=i<length-1 ==> arr[i] <= arr[i+1];
*/

/* fonction insert: on doit lui passer un bloc mémoire contenant length+1 cases
   (puisqu'on va insérer un élément), et trié. length doit être positif (on ne
   part pas d'un tableau vide.
   En sortie, le tableau est toujours trié, on ne modifie que les éléments entre
   0 et length, et on retrouve les mêmes éléments qu'avant plus celui qu'on a
   inséré.
*/
/*@ requires \valid_range(arr,0,length);
    requires length > 0;
    requires sorted(arr,length);
    behavior sorted:
      assigns arr[0..length];
      ensures sorted(arr,length+1);
    behavior elements:
    ensures \forall int v;
    (v!=val ==>
      nb_occ(arr,0,length,v) == nb_occ{Old}(arr,0,length-1,v));
    ensures
     nb_occ(arr,0,length,val) == nb_occ{Old}(arr,0,length-1,val)+1;
*/
void insert(int* arr, int length, int val);

/* fonction insert_sort: on part d'un bloc mémoire de taille length positive.
   À la fin de la fonction, le tableau est trié, on a modifié ses éléments entre
   0 et length (à l'exclusion d'éventuels autres), et le nombre d'occurences de
   chaque élément est identique à ce qu'on avait en début de fonction
*/

/*@ requires \valid_range(arr,0,length-1);
  requires length > 0;
  behavior sorted:
  assigns arr[0..length-1];
  ensures sorted(arr,length);
  behavior elements:
  ensures \forall int v; nb_occ(arr,0,length-1,v) ==
            nb_occ{Old}(arr,0,length-1,v);
 */
void insert_sort(int* arr, int length);

void insert(int* arr, int length, int val) {
  int i = length -1;
  /* invariant de boucle pour insert: on a décalé d'une case vers la droite
     les éléments d'indice i+1 et au dessus. Les autres éléments sont inchangés.
     Cela implique que les deux parties du tableau sont triées, le
     nombre d'occurence de chaque élément dans chacune des deux parties reste
     inchangé. De plus tous les éléments de la partie haute sont plus grands que
     val.
  */
  /*@
    for sorted: loop assigns arr[i+1..length];
    loop invariant -1<=i<length;
    for sorted, elements: loop invariant \forall integer j;
        0<=j<=i+1 ==> arr[j] == \at(arr[j],Pre);
    for sorted, elements: loop invariant \forall integer j;
            i<j<length ==> arr[j+1]==\at(arr[j],Pre);
    for sorted: loop invariant \forall integer j;
            i+1<=j<length ==> arr[j] <= arr[j+1];
    for sorted: loop invariant \forall integer j;
            i+1<j<=length ==> val < arr[j];
    for elements: loop invariant \forall int v;
        nb_occ(arr,0,i,v) == nb_occ{Pre}(arr,0,i,v);
    for elements: loop invariant \forall int v;
        nb_occ(arr,i+2,length,v) ==
         nb_occ{Pre}(arr,i+1,length-1,v);
    loop variant i;
   */
  while(i>=0 && arr[i] > val) { arr[i+1] = arr[i]; i--; }
  /* Les assertions ci-dessous reprennent les égalités sur les occurences des
     éléments qu'on a dans les invariants de boucle et que les prouveurs
     automatiques ont du mal à exploiter si on ne les guide pas.
  */
  /*@ for elements: assert \forall int v;
      nb_occ(arr,0,i,v) + nb_occ(arr,i+2,length,v) ==
      nb_occ{Pre}(arr,0,i,v) + nb_occ{Pre}(arr,i+1,length-1,v);
  */
  /*@ for elements: assert \forall int v;
      nb_occ(arr,0,i,v) + nb_occ(arr,i+2,length,v) ==
      nb_occ{Pre}(arr,0,length-1,v);
  */
  arr[i+1] = val;
  /*@ for elements: assert \forall int v;
      nb_occ(arr,0,i,v) + nb_occ(arr,i+2,length,v) ==
      nb_occ{Pre}(arr,0,i,v) + nb_occ{Pre}(arr,i+1,length-1,v);
  */
  /*@ for elements: assert \forall int v;
      nb_occ(arr,0,i,v) + nb_occ(arr,i+2,length,v) ==
      nb_occ{Pre}(arr,0,length-1,v);
  */
  /*@ for elements: assert nb_occ(arr,0,length,arr[i+1]) ==
       nb_occ(arr,0,i,arr[i+1]) + nb_occ(arr,i+2,length,arr[i+1]) + 1;
  */
  /*@ for elements: assert
    \forall int v; v!= arr[i+1] ==>
    nb_occ(arr,0,length,v) == nb_occ(arr,0,i,v) + nb_occ(arr,i+2,length,v);*/
  return;
}

void insert_sort(int* arr, int length)  {
  if (length > 0) {
    /* invariant de boucle pour insert_sort: le début du tableau est trié, on
       modifie seulement les premières cases du tableau, et les occurences dans
       les deux parties restent identiques.
     */
  /*@
    loop invariant 1<=i<=length;
    loop invariant sorted(arr,i);
    for sorted,elements: loop assigns arr[0..i];
    for elements: loop invariant \forall integer j; i<=j<length ==> arr[j]==\at(arr[j],Pre);
    for elements: loop invariant \forall int v;
    nb_occ(arr,0,i-1,v) == nb_occ{Pre}(arr,0,i-1,v);
    for elements: loop invariant \forall int v;
    nb_occ(arr,i,length-1,v) == nb_occ{Pre}(arr,i,length-1,v);
    loop variant length - i;
  */
      for(int i = 1; i < length; i++) {
        insert(arr,i,arr[i]);
        // Là encore, il faut aider un peu les prouveurs automatiques.
        /*@ for elements:
            assert nb_occ(arr,0,i,\at(arr[\at(i,Here)],Pre)) ==
            nb_occ{Pre}(arr,0,i-1,\at(arr[\at(i,Here)],Pre))+1;
        */
        /*@ for elements: assert \forall int v; v!=\at(arr[\at(i,Here)],Pre) ==>
          nb_occ(arr,0,i,v) == nb_occ{Pre}(arr,0,i-1,v);
        */
      }}
}

/*
Local Variables:
compile-command: "frama-c -jessie insert_sort_proved.c"
End:
*/
