open Cil_types

let typer _context _loc _tree = Ext_id 42
let short_printer _printer fmt _kind = Format.fprintf fmt "HS: some content"

let () =
  Acsl_extension.register_global "without_short" typer false ;
  Acsl_extension.register_global "has_short" typer ~short_printer false

let process_global _ = function
  | Dextended(e, _, _) -> Kernel.feedback "%a" Cil_printer.pp_short_extended e
  | _ -> ()

let () = Db.Main.extend (fun () -> Annotations.iter_global process_global)
