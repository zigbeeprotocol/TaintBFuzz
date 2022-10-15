open Cil_types

let e1 = Emitter.(create "emitter1" [ Code_annot ] ~correctness:[] ~tuning:[])
let e2 = Emitter.(create "emitter2" [ Code_annot ] ~correctness:[] ~tuning:[])

let mk_assigns e v =
  let lv = Cil.cvar_to_lvar v in
  let term_v  = Logic_const.tvar lv in
  let named_term_v =
    { term_v with
      term_name = ("added_by_"^(Emitter.get_name e))::term_v.term_name }
  in
  let id_v = Logic_const.new_identified_term named_term_v  in
  Writes[id_v,FromAny]

let add_assigns ?(keep_empty=false) e kf stmt v =
  Annotations.add_code_annot ~keep_empty e ~kf stmt
    (Logic_const.new_code_annotation
       (AAssigns ([], mk_assigns e v)));
  Filecheck.check_ast ("after insertion of loop assigns " ^ v.vname)

let mk_allocates e v =
  let lv = Cil.cvar_to_lvar v in
  let term_v = Logic_const.tvar lv in
  let named_term_v =
    { term_v with
      term_name = ("added_by_"^(Emitter.get_name e))::term_v.term_name }
  in
  let id_v = Logic_const.new_identified_term named_term_v in
  FreeAlloc ([],[id_v])

let add_allocates ?(keep_empty=false) e kf stmt v =
  Annotations.add_code_annot ~keep_empty e ~kf stmt
    (Logic_const.new_code_annotation (AAllocation([],mk_allocates e v)));
  Filecheck.check_ast ("after insertion of loop allocates " ^ v.vname )

let check_only_one f =
  let seen = ref false in
  fun _ a ->
    if f a then begin
      assert (not !seen);
      seen := true
    end

let filter_category f _ a acc = if f a then a :: acc else acc

let main () =
  Ast.compute();
  let kf = Globals.Functions.find_by_name "f" in
  let def = Kernel_function.get_definition kf in
  let s =
    List.find
      (fun s -> match s.skind with Loop _ -> true | _ -> false) def.sallstmts
  in
  let s2 =
    List.find
      (fun s' -> s!=s' && (match s'.skind with Loop _ -> true | _ -> false))
      def.sallstmts
  in
  let s3 = Kernel_function.find_return kf in
  let j = Cil.makeLocalVar def ~insert:true "j" Cil.intType in
  let k = Cil.makeLocalVar def ~insert:true "k" Cil.intType in
  let l = Cil.makeLocalVar def ~insert:true "l" Cil.intType in
  let p = Cil.makeLocalVar def ~insert:true "p" Cil.intPtrType in
  let q = Cil.makeLocalVar def ~insert:true "q" Cil.intPtrType in
  let r = Cil.makeLocalVar def ~insert:true "r" Cil.intPtrType in
  add_assigns e1 kf s j;
  add_assigns e2 kf s k;
  add_assigns e1 kf s l;
  add_assigns ~keep_empty:true e2 kf s2 j;
  Annotations.add_assigns ~keep_empty:true e1 kf ~stmt:s3 (mk_assigns e1 k);
  add_allocates e1 kf s p;
  add_allocates e2 kf s q;
  add_allocates e1 kf s r;
  add_allocates ~keep_empty:true e2 kf s2 p;
  Annotations.add_allocates ~keep_empty:true e1 kf ~stmt:s3 (mk_allocates e1 k);
  Annotations.iter_code_annot (check_only_one Logic_utils.is_assigns) s;
  Annotations.iter_code_annot (check_only_one Logic_utils.is_allocation) s;
  let lassigns =
    Annotations.fold_code_annot (filter_category Logic_utils.is_assigns) s []
  in
  assert (List.length lassigns = 1);
  let lalloc =
    Annotations.fold_code_annot (filter_category Logic_utils.is_allocation) s []
  in
  assert (List.length lalloc = 1);
  ignore
    (Property_status.get
       (Property.ip_of_code_annot_single kf s (List.hd lassigns)));
  ignore
    (Property_status.get
       (Property.ip_of_code_annot_single kf s (List.hd lalloc)));
  File.pretty_ast ()

let () = Db.Main.extend main
