typedef struct _list
  { int element; struct _list* next; } list;
/*@ inductive \action<alert@2>??<reachable??>\action<alert@4>??<{L}??>(list* root, list* node) {
      \action<alert@3>??<case reachable_hd\action<alert@4>??<{L}??>:??>
        \forall list* l1; reachable(l1,l1);
      \action<alert@3>??<case reachable_next\action<alert@4>??<{L}??>:??>
        \forall list* l1, *l2;
        \valid(l1) ==> reachable(l1->next,l2) ==>
        reachable(l1,l2);
}*/
