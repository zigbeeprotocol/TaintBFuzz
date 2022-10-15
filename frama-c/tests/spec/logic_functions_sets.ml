open Cil_types

let check = function
  | Dfun_or_pred (li, _) ->
    let decl_type = Option.get li.l_type in
    let body_type = match li.l_body with
      | LBterm t -> t.term_type
      | _ -> assert false
    in
    if 0 <> Cil_datatype.Logic_type.compare decl_type body_type then begin
      Kernel.failure "Bad type for: %a" Cil_datatype.Logic_info.pretty li
    end
  | _ -> ()

let () =
  Db.Main.extend (fun () -> Annotations.iter_global (fun _ g -> check g))
