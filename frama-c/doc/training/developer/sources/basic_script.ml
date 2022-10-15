(*# boilerplate *)
open Cil_types


(*# launch analysis *)
let nb_entry_points = ref 0

let run f () =
  Kernel.feedback "Using function %s as entry point" f;
  incr nb_entry_points;
  Kernel.MainFunction.set f;
  Kernel.LibEntry.on ();
  Eva.Analysis.compute ()

(*# Main driver function*)
let all_entry_points () =
  (*## Setting options. *)
  let files = [ "huffman.c"; "rice.c"; "shannonfano.c"; "lz.c"; "rle.c"; 
                "systimer.c" ]
  in
  let files = List.map (Filename.concat "bcl") files in
  Kernel.Files.set files;
  Dynamic.Parameter.Int.set "-slevel" 100;
  Dynamic.Parameter.Bool.on "-val-ignore-recursive-calls" ();
  (*## Parsing. *)
  Ast.compute ();
  (*## Find entry points *)
  Globals.Functions.iter
    (fun kf ->
      if Kernel_function.is_definition kf && 
        (Kernel_function.find_syntactic_callsites kf = [])
      then
        run (Kernel_function.get_name kf) ());
  Kernel.feedback "Analyzed %d potential entry points" !nb_entry_points

(*# Basic script *)
(* let () = Db.Main.extend (run "main") *)

(*# Register driver function *)
let () = Db.Main.extend all_entry_points

(*# *)
(*
Local Variables:
mode: outline-minor
mode: linum
outline-regexp: " *(\\*#+"
End:
*)
