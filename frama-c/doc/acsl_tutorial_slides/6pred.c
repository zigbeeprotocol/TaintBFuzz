/* USER-DEFINED PREDICATES */

typedef 
  struct _list 
    { int element; 
      struct _list* next; } list;

/* NULL is the empty list */



/*@ predicate reachable{L}(list* root, list* node) =
        root == node ||
        \valid(root) && reachable(root -> next, node);
*/



/*@ predicate finite_list{L}(list* root) = 
                        reachable(root,\null);
*/
