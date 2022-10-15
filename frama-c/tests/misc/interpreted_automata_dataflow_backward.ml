open Cil_types

module Set = Cil_datatype.Varinfo.Set

module LivenessDomain =
struct
  type t = Set.t

  let initial = Set.empty

  let pretty fmt v =
    Pretty_utils.pp_iter ~sep:",@ " Set.iter Cil_datatype.Varinfo.pretty fmt v

  let join v1 v2 =
    Set.union v1 v2

  let widen v1 v2 =
    if Set.subset v2 v1 then
       None (* Inclusion *)
    else
      Some v2 (* No widening necessary *)

  let rec vars exp =
    match exp.enode with
    | Const _
    | SizeOf _ | SizeOfE _ | SizeOfStr _
    | AlignOf _ | AlignOfE _
    | AddrOf _ | StartOf _ ->
      Set.empty
    | UnOp (_, e, _) | CastE (_,e) ->
      vars e
    | BinOp (_, e1, e2, _) ->
      Set.union (vars e1) (vars e2)
    | Lval (Var vi, _) -> Set.singleton vi
    | Lval (Mem e, _) -> vars e

  let transfer t v =
    let open Interpreted_automata in
    let r = match t with
    | Skip | Prop _ | Leave _ | Return (None,_) ->
      v (* Nothing to do *)
    | Enter b ->
      Set.diff v (Set.of_list b.blocals) (* If unconditionnaly initialized, they should not be there *)
    | Instr (Set ((Var vi, NoOffset), exp, _), _)
    | Instr (Local_init (vi, AssignInit (SingleInit exp), _), _) ->
      Set.union (Set.remove vi v) (vars exp)
    | Guard (exp,_,_)
    | Instr (Set (_, exp, _), _)
    | Return (Some exp, _) ->
      Set.union v (vars exp)
    | Instr _ ->
      v (* All remaining cases are incorrectly ignored *)
    in
    Some r
end


module Dataflow = Interpreted_automata.BackwardAnalysis (LivenessDomain)

let run () =
  let main_kf, _ = Globals.entry_point () in
  (* Run the analysis *)
  let results = Dataflow.fixpoint main_kf LivenessDomain.initial in
  (* Output to dot *)
  let filepath =
    let open Filename in
    (remove_extension (basename __FILE__) ^ ".dot")
  in
  let filepath = Filepath.Normalized.of_string filepath in
  Dataflow.Result.to_dot_file LivenessDomain.pretty results filepath

let () =
  Db.Main.extend run
