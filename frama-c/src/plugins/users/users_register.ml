(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

(**  @plugin development guide *)

include
  Plugin.Register
    (struct
      let name = "users"
      let shortname = "users"
      let help = "function callees"
    end)

(** @plugin development guide *)
module ForceUsers =
  False
    (struct
      let option_name = "-users"
      let help = "compute function callees"
    end)

module Users =
  Kernel_function.Make_Table
    (Kernel_function.Hptset)
    (struct
      let name = "Users"
      let size = 17
      let dependencies = [ Eva.Analysis.self; ForceUsers.self ]
    end)

let compute_users _ =
  let process kf =
    if Eva.Results.is_called kf
    then
      let callstacks = Eva.Results.(at_start_of kf |> callstacks) in
      let process_callstack list =
        let process_element (user, _call_site) =
          ignore
            (Users.memo
               ~change:(Kernel_function.Hptset.add kf)
               (fun _ -> Kernel_function.Hptset.singleton kf)
               user)
        in
        List.iter process_element (List.tl list)
      in
      List.iter process_callstack callstacks
  in
  Globals.Functions.iter process;
  Users.mark_as_computed ()

let add_eva_hook () =
  Eva.Analysis.(register_computation_hook ~on:Computed compute_users)

let init () = if ForceUsers.get () then add_eva_hook ()
let () = Cmdline.run_after_configuring_stage init

let get kf =
  let find kf =
    try Users.find kf
    with Not_found -> Kernel_function.Hptset.empty
  in
  if Users.is_computed () then
    find kf
  else begin
    if Eva.Analysis.is_computed () then begin
      feedback "requiring again the computation of the value analysis";
      Project.clear
        ~selection:(State_selection.with_dependencies Eva.Analysis.self)
        ()
    end else
      feedback ~level:2 "requiring the computation of the value analysis";
    Eva.Analysis.compute ();
    compute_users ();
    find kf
  end

let get =
  Journal.register
    "Users.get"
    (Datatype.func Kernel_function.ty Kernel_function.Hptset.ty)
    get

let print () =
  if ForceUsers.get () then
    result "@[<v>====== DISPLAYING USERS ======@ %t\
            ====== END OF USERS =========="
      (fun fmt ->
         Callgraph.Uses.iter_in_rev_order
           (fun kf ->
              let callees = get kf in
              if not (Kernel_function.Hptset.is_empty callees) then
                Format.fprintf fmt "@[<hov 4>%a: %a@]@ "
                  Kernel_function.pretty kf
                  (Pretty_utils.pp_iter
                     ~pre:"" ~sep:"@ " ~suf:"" Kernel_function.Hptset.iter
                     Kernel_function.pretty)
                  callees))

let print_once, _self_print =
  State_builder.apply_once "Users_register.print" [ Users.self ] print

let () = Db.Main.extend print_once

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
