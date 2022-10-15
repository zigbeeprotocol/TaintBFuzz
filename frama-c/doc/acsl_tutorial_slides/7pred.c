/* PROLOG-STYLE DEFINITION OF A LOGIC FUNCTION */

typedef 
  struct _list 
    { int element; 
      struct _list* next; } list;

/* NULL is the empty list */


/*@ logic integer length{L}(list* l);
*/

/*@ axiom length_nil: length(\null) == 0; 
*/

/*@ axiom length_cons{L}:
      \forall list* l, integer n;
      \valid(l) ==> length(l) == length(l->next) + 1;
*/


/*@ predicate finite_list{L}(list* root) = 
      \exists int n; n == length(root);
*/
