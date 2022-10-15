/*@ inductive Permut{L1,L2}
      (int a[], integer l, integer h) {
     case Permut_trans{L1,L2,L3}:
       \forall int a[], integer l, h;
         Permut{L1,L2}(a, l, h) &&
         Permut{L2,L3}(a, l, h) ==>
           Permut{L1,L3}(a,l, h) ;
     case Permut_swap{L1,L2}: ...
    }
@*/
