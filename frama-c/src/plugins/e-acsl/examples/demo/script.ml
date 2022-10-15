open Cil_types

(* ************************************************************************** *)
(* Registering the plug-in *)
(* ************************************************************************** *)

include Plugin.Register(struct
    let name = "txt2ppt"
    let shortname = "t2p"
    let help = "Convert E-ACSL textual properties to Frama-C properties"
  end)

(* ************************************************************************** *)
(* Defining plug-in's options *)
(* ************************************************************************** *)

module Fct_name =
  Empty_string
    (struct
      let option_name = "-ppt-fct"
      let help = "Name of the function in which the property is defined"
      let arg_name = ""
    end)

module Ppt_name =
  Empty_string
    (struct
      let option_name = "-ppt-name"
      let help = "Name of the property (assertion, ...)"
      let arg_name = ""
    end)

module Ppt_line =
  Zero
    (struct
      let option_name = "-ppt-line"
      let help = "Line at which the property is defined"
      let arg_name = ""
    end)

(* ************************************************************************** *)
(* Searching the property according to plug-in's options *)
(* ************************************************************************** *)

exception Found of Property.t * int

let search_assert_or_invariant kf =
  try
    Annotations.iter_all_code_annot
      (fun stmt _ a ->
         match a.annot_content with
         | AAssert(_, _, p) | AInvariant(_, _, p) ->
           let line = Ppt_line.get () in
           if (fst (p.loc)).Lexing.pos_lnum = line then
             raise (Found(Property.ip_of_code_annot_single kf stmt a, line))
         | _ -> ());
    assert false
  with Found(ppt, line) ->
    ppt, line

let is_predicate p line = (fst (p.ip_loc)).Lexing.pos_lnum = line

let search_funspec_part iter convert kf =
  try
    Annotations.iter_behaviors
      (fun _ bhv -> iter (fun _ a -> convert bhv a) kf bhv.b_name)
      kf;
    assert false
  with Found(ppt, line) ->
    ppt, line

let search_ensures kf =
  search_funspec_part
    Annotations.iter_ensures
    (fun bhv (_, p as a) ->
       let line = Ppt_line.get () in
       if is_predicate p line then
         raise (Found (Property.ip_of_ensures kf Kglobal bhv a, line)) )
    kf

let search_requires kf =
  search_funspec_part
    Annotations.iter_requires
    (fun bhv a ->
       let line = Ppt_line.get () in
       if is_predicate a line then
         raise (Found (Property.ip_of_requires kf Kglobal bhv a, line)) )
    kf

let search kf = match Ppt_name.get () with
  | "" | "Assertion" | "Invariant" -> search_assert_or_invariant kf
  | "Precondition" -> search_requires kf
  | "Postcondition" -> search_ensures kf
  | s -> abort "unknown property %s" s

(* ************************************************************************** *)
(* Emitting status "invalid" for the property   *)
(* ************************************************************************** *)

let emitter =
  Emitter.create "E-ACSL" [ Emitter.Property_status ] ~correctness:[] ~tuning:[]

let emit ppt line =
  feedback "@[line %d:@ %a@ is@ invalid.@]" line Property.pretty ppt;
  Property_status.emit emitter ~hyps:[] ppt Property_status.False_and_reachable

(* ************************************************************************** *)
(* Plug-in's main *)
(* ************************************************************************** *)

let main () =
  let kf = Globals.Functions.find_by_name (Fct_name.get ()) in
  let ppt, line = search kf in
  emit ppt line

let () = Db.Main.extend main
