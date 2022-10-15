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

(* --- Registration types --------------------------------------------------- *)

type 'v value =
  | Single of (module Abstract_value.Leaf with type t = 'v)
  | Struct of 'v Abstract.Value.structure

type precise_loc = Precise_locs.precise_location

module type leaf_domain = Abstract_domain.Leaf with type location = precise_loc

module type domain_functor =
  functor (Value: Abstract.Value.External) ->
    (leaf_domain with type value = Value.t)

type 'v domain =
  | Domain: (module leaf_domain with type value = 'v) -> 'v domain
  | Functor: (module domain_functor) -> _ domain

type 'v abstraction =
  { values: 'v value;
    domain: 'v domain; }

type 't with_info =
  { name: string;
    experimental: bool;
    priority: int;
    abstraction: 't; }

type flag = Flag: 'v abstraction with_info -> flag

(* --- Config and registration ---------------------------------------------- *)

module Config = struct
  module OptMode = Datatype.Option (Domain_mode)
  module Element = struct
    type t = flag * Domain_mode.t option

    (* Flags are sorted by increasing priority order, and then by name. *)
    let compare (Flag f1, mode1) (Flag f2, mode2) =
      let c = Datatype.Int.compare f1.priority f2.priority in
      if c <> 0 then c else
        let c = Datatype.String.compare f1.name f2.name in
        if c <> 0 then c else
          OptMode.compare mode1 mode2
  end

  include Set.Make (Element)

  let mem (Flag domain) =
    exists (fun (Flag flag, _mode) -> flag.name = domain.name)

  let abstractions = ref []
  let dynamic_abstractions = ref []

  let register_domain_option ~name ~experimental ~descr =
    let descr = if experimental then "Experimental. " ^ descr else descr in
    Parameters.register_domain ~name ~descr

  let register ~name ~descr ?(experimental=false) ?(priority=0) abstraction =
    register_domain_option ~name ~experimental ~descr;
    let flag = Flag { name; experimental; priority; abstraction } in
    abstractions := flag :: !abstractions;
    flag

  let dynamic_register ~name ~descr ?(experimental=false) ?(priority=0) make =
    register_domain_option ~name ~experimental ~descr;
    let make' () : flag =
      Flag { name; experimental; priority; abstraction = make () }
    in
    dynamic_abstractions := (name,make') :: !dynamic_abstractions

  let configure () =
    let add_main_mode mode =
      let main, _ = Globals.entry_point () in
      (main, Domain_mode.Mode.all) :: mode
    in
    let add config (name, make) =
      let enabled = Parameters.Domains.mem name in
      try
        let mode = Parameters.DomainsFunction.find name in
        let mode = if enabled then add_main_mode mode else mode in
        add (make (), Some mode) config
      with Not_found ->
        if enabled then add (make (), None) config else config
    in
    let aux config (Flag domain as flag) =
      add config (domain.name, (fun () -> flag))
    in
    let config = List.fold_left aux empty !abstractions in
    List.fold_left add config !dynamic_abstractions

  (* --- Register default abstractions -------------------------------------- *)

  let create_domain ?experimental priority name descr values domain =
    let abstraction = { values = Single values; domain = Domain domain } in
    register ~name ~descr ~priority ?experimental abstraction

  (* Register standard domains over cvalues. *)
  let make ?experimental rank name descr =
    create_domain ?experimental rank name descr (module Main_values.CVal)

  let cvalue =
    make 9 "cvalue"
      "Main analysis domain, enabled by default. Should not be disabled."
      (module Cvalue_domain.State)

  let symbolic_locations =
    make 7 "symbolic-locations"
      "Infers values of symbolic locations represented by imprecise lvalues, \
       such as t[i] or *p when the possible values of [i] or [p] are imprecise."
      (module Symbolic_locs.D)

  let equality =
    let descr = "Infers equalities between syntactic C expressions. \
                 Makes the analysis less dependent on temporary variables and \
                 intermediate computations."
    and abstraction =
      { values = Struct Abstract.Value.Unit;
        domain = Functor (module Equality_domain.Make); }
    in
    register ~name:"equality" ~descr ~priority:8 abstraction

  let gauges =
    make 6 "gauges"
      "Infers linear inequalities between the variables modified within a loop \
       and a special loop counter."
      (module Gauges_domain.D)

  let octagon =
    make 6 "octagon"
      "Infers relations between scalar variables of the form b ≤ ±X ± Y ≤ e, \
       where X, Y are program variables and b, e are constants."
      (module Octagons)

  let bitwise =
    create_domain 3 "bitwise"
      "Infers bitwise information to interpret more precisely bitwise operators."
      (module Offsm_value.Offsm) (module Offsm_domain.D)

  let sign =
    create_domain 4 "sign"
      "Infers the sign of program variables."
      (module Sign_value) (module Sign_domain)

  let inout = make 5 "inout" ~experimental:true
      "Infers the inputs and outputs of each function."
      (module Inout_domain.D)

  let traces =
    make 2 "traces" ~experimental:true
      "Builds an over-approximation of all the traces that lead \
       to a statement."
      (module Traces_domain.D)

  let printer =
    make 2 "printer"
      "Debug domain, only useful for developers. Prints the transfer functions \
       used during the analysis."
      (module Printer_domain)

  (* --- Default and legacy configurations ---------------------------------- *)

  let default = configure ()
  let legacy = singleton (cvalue, None)
end

let register = Config.register
let dynamic_register = Config.dynamic_register

(* --- Building value abstractions ------------------------------------------ *)

module Leaf_Value (V: Abstract_value.Leaf) = struct
  include V
  let structure = Abstract.Value.Leaf (V.key, (module V))
end

module Leaf_Location (Loc: Abstract_location.Leaf) = struct
  include Loc
  let structure = Abstract.Location.Leaf (Loc.key, (module Loc))
end

module Leaf_Domain (D: Abstract_domain.Leaf) = struct
  include D
  let structure = Abstract.Domain.Leaf (D.key, (module D))
end

module type Acc = sig
  module Val : Abstract.Value.External
  module Loc : Abstract.Location.Internal with type value = Val.t
                                           and type location = precise_loc
  module Dom : Abstract.Domain.Internal with type value = Val.t
                                         and type location = Loc.location
end

module Internal_Value = struct
  open Abstract.Value

  type value_key_module =  V : 'v key * 'v data -> value_key_module

  let open_value_abstraction (module Value : Internal) =
    (module struct
      include Value
      include Structure.Open (Abstract.Value) (Value)
    end : Abstract.Value.External)

  let add_value_leaf value (V (key, v)) =
    let module Value = (val open_value_abstraction value) in
    if Value.mem key then value else
      (module struct
        include Value_product.Make (Value) (val v)
        let structure = Node (Value.structure, Leaf (key, v))
      end)

  let void_value () =
    Self.fatal
      "Cannot register a value module from a Void structure."

  let add_value_structure value internal =
    let rec aux: type v. (module Internal) -> v structure -> (module Internal) =
      fun value -> function
        | Option (s, _) -> aux value s
        | Leaf (key, v) -> add_value_leaf value (V (key, v))
        | Node (s1, s2) -> aux (aux value s1) s2
        | Unit -> value
        | Void -> void_value ()
    in
    aux value internal

  let build_values config initial_value =
    let build (Flag flag, _) acc =
      match flag.abstraction.values with
      | Struct structure -> add_value_structure acc structure
      | Single (module V) -> add_value_leaf acc (V (V.key, (module V)))
    in
    let value = Config.fold build config initial_value in
    open_value_abstraction value


  module Convert
      (Value: Abstract.Value.External)
      (Struct: sig type v val s : v value end)
  = struct

    let structure = match Struct.s with
      | Single (module V) -> Abstract.Value.Leaf (V.key, (module V))
      | Struct s -> s

    type extended_value = Value.t

    let replace_val =
      let rec set: type v. v structure -> v -> Value.t -> Value.t =
        function
        | Leaf (key, _) -> Value.set key
        | Node (s1, s2) ->
          let set1 = set s1 and set2 = set s2 in
          fun (v1, v2) value -> set1 v1 (set2 v2 value)
        | Option (s, default) -> fun v -> set s (Option.value ~default:default v)
        | Unit -> fun () value -> value
        | Void -> void_value ()
      in
      set structure

    let extend_val v = replace_val v Value.top

    let restrict_val =
      let rec get: type v. v structure -> Value.t -> v = function
        | Leaf (key, _) -> Option.get (Value.get key)
        | Node (s1, s2) ->
          let get1 = get s1 and get2 = get s2 in
          fun v -> get1 v, get2 v
        | Option (s, _) -> fun v -> Some (get s v)
        | Unit -> fun _ -> ()
        | Void -> void_value ()
      in
      get structure

    type extended_location = Main_locations.PLoc.location

    let restrict_loc = fun x -> x
    let extend_loc = fun x -> x
  end
end

(* --- Building domain abstractions ----------------------------------------- *)

module type internal_loc =
  Abstract.Location.Internal with type location = precise_loc
module type internal_domain =
  Abstract.Domain.Internal with type location = precise_loc

let eq_value:
  type a b. a Abstract.Value.structure -> b value -> (a,b) Structure.eq option
  = fun structure -> function
    | Struct s -> Abstract.Value.eq_structure structure s
    | Single (module V) ->
      match structure with
      | Abstract.Value.Leaf (key, _) -> Abstract.Value.eq_type key V.key
      | _ -> None

let add_domain (type v) dname mode (abstraction: v abstraction) (module Acc: Acc) =
  let domain : (module internal_domain with type value = Acc.Val.t) =
    match abstraction.domain with
    | Functor make ->
      let module Make = (val make: domain_functor) in
      (module Leaf_Domain (Make (Acc.Val)))
    | Domain domain ->
      match eq_value Acc.Val.structure abstraction.values with
      | Some Structure.Eq ->
        let module Domain = (val domain) in
        (module Leaf_Domain (Domain))
      | None ->
        let module Domain = (val domain : leaf_domain with type value = v) in
        let module Struct = struct
          type v = Domain.value
          let s = abstraction.values
        end in
        let module Convert = Internal_Value.Convert (Acc.Val) (Struct) in
        (module Domain_lift.Make (Domain) (Convert))
  in
  (* Set the name of the domain. *)
  let module Domain = struct
    include (val domain)
    let name = dname
    module Store = struct
      include Store
      let register_global_state storage state =
        let no_results = Parameters.NoResultsDomains.mem dname in
        register_global_state (storage && not no_results) state
    end
  end in
  (* Restricts the domain according to [mode]. *)
  let domain : (module internal_domain with type value = Acc.Val.t) =
    match mode with
    | None -> (module Domain)
    | Some kf_modes ->
      let module Scope = struct let functions = kf_modes end in
      let module Domain =
        Domain_builder.Restrict
          (Acc.Val)
          (Domain)
          (Scope)
      in
      (module Domain)
  in
  let domain : (module internal_domain with type value = Acc.Val.t) =
    match Abstract.Domain.(eq_structure Acc.Dom.structure Unit) with
    | Some _ -> domain
    | None ->
      (* The new [domain] becomes the left leaf of the domain product, and will
         be processed before the domains from [Acc.Dom] during the analysis. *)
      (module Domain_product.Make (Acc.Val) ((val domain)) (Acc.Dom))
  in
  (module struct
    module Val = Acc.Val
    module Loc = Acc.Loc
    module Dom = (val domain)
  end : Acc)

let warn_experimental flag =
  if flag.experimental then
    Self.(warning ~wkey:wkey_experimental
            "The %s domain is experimental." flag.name)

let build_domain config abstract =
  let build (Flag flag, mode) acc =
    warn_experimental flag;
    add_domain flag.name mode flag.abstraction acc
  in
  (* Domains in the [config] are sorted by increasing priority: domains with
     higher priority are added last: they will be at the top of the domains
     tree, and thus will be processed first during the analysis. *)
  Config.fold build config abstract


(* --- Value reduced product ----------------------------------------------- *)

module type Value = sig
  include Abstract.Value.External
  val reduce : t -> t
end

module type S = sig
  module Val : Value
  module Loc : Abstract.Location.External with type value = Val.t
  module Dom : Abstract.Domain.External with type value = Val.t
                                         and type location = Loc.location
end

module type Eva = sig
  include S
  module Eval: Evaluation.S with type state = Dom.t
                             and type value = Val.t
                             and type loc = Loc.location
                             and type origin = Dom.origin
end


type ('a, 'b) value_reduced_product =
  'a Abstract.Value.key * 'b Abstract.Value.key * ('a -> 'b -> 'a * 'b)

type v_reduced_product = R: ('a, 'b) value_reduced_product -> v_reduced_product

let value_reduced_product = ref []

let register_value_reduction reduced_product =
  value_reduced_product := (R reduced_product) :: !value_reduced_product

(* When the value abstraction contains both a cvalue and an interval
   component (coming currently from an Apron domain), reduce them from each
   other. If the Cvalue is not a scalar do nothing, because we do not
   currently use Apron for pointer offsets. *)
let reduce_apron_itv cvalue ival =
  match ival with
  | None -> begin
      try cvalue, Some (Cvalue.V.project_ival cvalue)
      with Cvalue.V.Not_based_on_null -> cvalue, ival
    end
  | Some ival ->
    try
      let ival' = Cvalue.V.project_ival cvalue in
      if Ival.is_int ival'
      then
        let reduced_ival = Ival.narrow ival ival' in
        let cvalue = Cvalue.V.inject_ival reduced_ival in
        cvalue, Some reduced_ival
      else cvalue, Some ival
    with Cvalue.V.Not_based_on_null -> cvalue, Some ival

let () =
  register_value_reduction
    (Main_values.CVal.key, Main_values.Interval.key, reduce_apron_itv)

module Reduce (Value : Abstract.Value.External) = struct
  include Value

  let make_reduction acc (R (key1, key2, f)) =
    match Value.get key1, Value.get key2 with
    | Some get1, Some get2 ->
      let set1 = Value.set key1
      and set2 = Value.set key2 in
      let reduce v = let v1, v2 = f (get1 v) (get2 v) in set1 v1 (set2 v2 v) in
      reduce :: acc
    | _, _ -> acc

  let reduce =
    let list = List.fold_left make_reduction [] !value_reduced_product in
    fun v -> List.fold_left (fun v reduce -> reduce v) v list
end

(* --- Final hook ----------------------------------------------------------- *)

let final_hooks = ref []

let register_hook f =
  final_hooks := f :: !final_hooks

let apply_final_hooks abstractions =
  List.fold_left (fun acc f -> f acc) abstractions !final_hooks

(* --- Building abstractions ------------------------------------------------ *)

module Open (Acc: Acc) : S = struct
  module Val = Reduce (Acc.Val)
  module Loc = struct
    include Acc.Loc
    include Structure.Open (Abstract.Location)
        (struct include Acc.Loc type t = location end)
  end
  module Dom = struct
    include Acc.Dom
    include Structure.Open (Abstract.Domain) (Acc.Dom)

    let get_cvalue = match get Cvalue_domain.State.key with
      | None -> None
      | Some get -> Some (fun s -> fst (get s))

    let get_cvalue_or_top = match get Cvalue_domain.State.key with
      | None -> fun _ -> Cvalue.Model.top
      | Some get -> fun s -> fst (get s)

    let get_cvalue_or_bottom = function
      | `Bottom -> Cvalue.Model.bottom
      | `Value state -> get_cvalue_or_top state
  end
end

module CVal = Leaf_Value (Main_values.CVal)

let unit_acc (module Value: Abstract.Value.External) =
  let loc : (module internal_loc with type value = Value.t) =
    match Abstract.Value.eq_structure Value.structure CVal.structure with
    | Some Structure.Eq -> (module Leaf_Location (Main_locations.PLoc))
    | _ ->
      let module Struct = struct
        type v = Cvalue.V.t
        let s = Single (module Main_values.CVal)
      end in
      let module Conv = Internal_Value.Convert (Value) (Struct) in
      (module Location_lift.Make (Main_locations.PLoc) (Conv))
  in
  (module struct
    module Val = Value
    module Loc = (val loc)
    module Dom = Unit_domain.Make (Val) (Loc)
  end : Acc)

let build_abstractions config =
  let initial_value : (module Abstract.Value.Internal) =
    if Config.mem Config.bitwise config
    then (module Offsm_value.CvalueOffsm)
    else (module CVal)
  in
  let value = Internal_Value.build_values config initial_value in
  let acc = unit_acc value in
  build_domain config acc

let configure = Config.configure

let make config =
  let abstractions = build_abstractions config in
  let abstractions = (module Open (val abstractions): S) in
  apply_final_hooks abstractions

module Default = (val make Config.default)
module Legacy = (val make Config.legacy)
