(* On nomme H le module des hypothèses. *)
module H = AlgoH ;;

(* produit une nouvelle fonction spécialisée en partant de [ff]
   en marquant l'élément [e] et toutes ses dépendances avec la marque [m]. *)
let rec mark_rec_pdg_elem pdg stmt_elems m e ff =
  let new_ff = add_elem_mark pdg stmt_elems m e ff in
  let dpds = H.get_dpds e pdg in
    List.fold_right (mark_rec_pdg_elem pdg stmt_elems m) dpds new_ff
  (* ;; *)
and
(* [add_elem_mark] ajoute la marque [m] à l'instruction correspondant à
   l'élément [e] et marque les autres éléments éventuels comme superflus. *)
      add_elem_mark pdg stmt_elems m e ff = 
  let stmt = H.get_stmt e stmt_elems in
  let old_m = H.get_stmt_mark stmt ff in
  let new_m = H.combine_mark old_m m in
  let new_ff = H.replace_stmt_mark ff stmt new_m in
  let elems = H.get_elems stmt stmt_elems in
  let (_, other_elems) = List.partition (fun elem -> elem = e) elems in
  let mark_spare_elem e ff = mark_rec_pdg_elem pdg stmt_elems H.spare_mark e ff in
    List.fold_right mark_spare_elem other_elems new_ff
