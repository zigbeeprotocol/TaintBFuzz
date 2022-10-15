open Cabs
open Crowbar

let loc = Cabshelper.cabslu

let gen_int_type =
  choose [
    const Tint;
    const Tlong;
    const Tunsigned;
  ]

let gen_type =
  choose [
    gen_int_type;
    const Tfloat;
    const Tdouble;
  ]

let mk_exp expr_node = { expr_loc = loc; expr_node }

let needs_int_unary = function
  | NOT | BNOT -> true
  | _ -> false

let gen_unary =
  choose [
    const NOT;
    const BNOT;
    const MINUS;
    const PLUS;
  ]

(* NB: we don't generate shifts and division/modulo operands to avoid
   undefined operations. Overflows alarms are deactivated as well. *)

let needs_int_binary = function
  | AND | OR | BAND | BOR | XOR -> true
  | _ -> false

let gen_binary =
  choose [
    const AND;
    const OR;
    const BAND;
    const BOR;
    const XOR;
    const ADD;
    const SUB;
    const MUL;
    const EQ;
    const NE;
    const LT;
    const GT;
    const LE;
    const GE;
  ]

(* int32 generator as the default machdep is 32 bit.
   Moreover, we only generate positive integers here, as negative ones are
   supposed to be given by unary -
*)
let gen_constant =
  choose [
    map [ range 4 ]
      (fun i -> mk_exp (CONSTANT (CONST_INT (string_of_int i))));
    map [ float ]
      (fun f ->
         let up = 4.0 in
         let f = if f < 0.0 then 0. else f in
         let f = if f > up then up else f in
         mk_exp (CONSTANT (CONST_FLOAT (string_of_float f))))
  ]

let mk_cast t e = mk_exp (CAST (([SpecType t],JUSTBASE), SINGLE_INIT e))

let protected_cast t e =
  let max = mk_exp (CONSTANT(CONST_INT("255"))) in
  let min =
    match t with
    | Tunsigned -> mk_exp(CONSTANT(CONST_INT("0")))
    | _ ->  mk_exp (UNARY(MINUS,max))
  in
  let maxr = mk_cast t max in
  let minr = mk_cast t min in
  mk_exp(
    QUESTION(
      mk_exp(BINARY(GE,e,min)),
      mk_exp(QUESTION(mk_exp(BINARY(LE,e,max)),e,maxr)),
      minr))

let force_int typ e =
  let e = protected_cast typ e in
  mk_exp (CAST (([SpecType typ],JUSTBASE), SINGLE_INIT e))

let gen_expr =
  fix
    (fun gen_expr ->
       choose [
         gen_constant;
         map [ gen_int_type; gen_unary; gen_expr]
           (fun t u e ->
              let e = if needs_int_unary u then force_int t e else e in
              mk_exp (UNARY(u,e)));
         map [ gen_int_type; gen_binary; gen_expr; gen_expr ]
           (fun t b e1 e2 ->
              let e1,e2 =
                if needs_int_binary b then
                  force_int t e1, force_int t e2
                else e1,e2
              in
              mk_exp (BINARY (b,e1,e2)));
         map [ gen_expr; gen_expr; gen_expr ]
           (fun c et ef -> mk_exp (QUESTION (c,et,ef)));
         map [ gen_type; gen_expr ]
           (fun t e ->
              let e = protected_cast t e in
              mk_exp (CAST (([SpecType t],JUSTBASE), SINGLE_INIT e)));
       ])

let gen_cabs typ expr =
  let expr = protected_cast typ expr in
  (Datatype.Filepath.dummy,
   [ false,
     DECDEF(
       None,
       ([SpecType typ],
        [("a",
          ARRAY(JUSTBASE,[],{ expr_loc = loc; expr_node = NOTHING}),[],loc),
         COMPOUND_INIT [NEXT_INIT, SINGLE_INIT expr]]),
       loc);
     false,
     DECDEF(None,([SpecType Tint],[("result", JUSTBASE,[],loc),NO_INIT]),loc);
     false,
     FUNDEF(
      None,([SpecType Tvoid],("f", PROTO(JUSTBASE,[],[],false),[],loc)),
      { blabels = [];
        battrs = [];
        bstmts = [
          { stmt_ghost = false;
            stmt_node =
              DEFINITION(
                DECDEF(
                  None,
                  ([SpecType typ], [("x",JUSTBASE,[],loc),SINGLE_INIT expr]),
                  loc))};
          { stmt_ghost = false;
            stmt_node =
              COMPUTATION(
                mk_exp(
                  BINARY(
                    ASSIGN,
                    mk_exp (VARIABLE "result"),
                    mk_exp (
                      BINARY(
                        EQ,
                        mk_exp (VARIABLE "x"),
                        mk_exp(
                          INDEX(
                            mk_exp (VARIABLE "a"),
                            mk_exp (CONSTANT (CONST_INT "0")))))))), loc)}
          ]
      },
    loc,loc)])

let () = Kernel.AutoLoadPlugins.off()

let () = Project.set_current (Project.create "my_project")

let () = Dynamic.set_module_load_path [ "lib/plugins" ]

let () = Dynamic.load_module "frama-c-eva"

let on_from_name s f = Project.on (Project.from_unique_name s) f ()

let () =
  Cmdline.(
    parse_and_boot
      ~on_from_name:{ on_from_name }
      ~get_toplevel:(fun () f -> f ())
      ~play_analysis:(fun _ -> ()))

let run typ expr =
  Project.clear ();
  let loc = Cil_datatype.Location.unknown in
  let cabs = gen_cabs typ expr in
  Kernel.SignedOverflow.off ();
  Kernel.SignedDowncast.off ();
  Kernel.UnsignedOverflow.off ();
  Kernel.UnsignedDowncast.off ();
  Kernel.add_debug_keys Kernel.dkey_constfold;
  (* otherwise, we must load scope in addition to eva. *)
  Dynamic.Parameter.Bool.off "-eva-remove-redundant-alarms" ();
  Errorloc.clear_errors ();
  Format.printf "Cabs is@\n%a@." Cprint.printFile cabs;
  let cil =
    try Cabs2cil.convFile cabs
    with exn ->
      failf "Failed to typecheck cabs: %s@\n%a@."
        (Printexc.to_string exn)
        Cprint.printFile cabs
  in
  if Errorloc.had_errors () then begin
    failf "Failed to typecheck cabs (had errors)@\n%a@."
      Cprint.printFile cabs
  end;
  File.prepare_cil_file cil;
  Kernel.MainFunction.set "f";
  Eva.Analysis.compute ();
  let kf = Globals.Functions.find_by_name "f" in
  let r = Globals.Vars.find_from_astinfo "result" Cil_types.VGlobal in
  let ret = Kernel_function.find_return kf in
  let state = Db.Value.get_stmt_state ret in
  let v1 =
    !Db.Value.eval_expr
      ~with_alarms:CilE.warn_none_mode state (Cil.evar ~loc r)
  in
  let itv =
    try Cvalue.V.project_ival v1
    with exn ->
      failf "Eva analysis did not reduce to a constant: %s@\n%t@."
        (Printexc.to_string exn)
        (fun fmt -> File.pretty_ast ~fmt ())
  in
  if not (Ival.is_one itv) then begin
    failf "const fold did not reduce to identical value:@\n%t@."
      (fun fmt -> File.pretty_ast ~fmt ())
  end

let () = add_test ~name:"constfold" [gen_type; gen_expr] run
