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

open Eval
open Offsm_value

let store_redundant = false
(** If [true], the offsetmap domain stores information that can probably be
    re-synthesized from the value domain. Otherwise, we try to avoid such
    redundancies. Setting this variable to [true] is helpful to find
    unsoundnesses in the domain through testing, because many more expressions
    end up being handled. *)

let dkey = Self.register_category "d-bitwise"

module Default_offsetmap = struct
  open Cvalue

  let is_top m = V_Offsetmap.is_same_value m V_Or_Uninitialized.top

  let default_offsetmap b =
    match b with
    | Base.String _ ->
      Cvalue.Default_offsetmap.default_offsetmap b
    | Base.Var _ | Base.CLogic_Var _ | Base.Null | Base.Allocated _ ->
      let validity = Base.validity b in
      match V_Offsetmap.size_from_validity validity with
      | `Bottom -> `Bottom
      | `Value size ->
        `Value (V_Offsetmap.create_isotropic ~size V_Or_Uninitialized.top)

  let default_contents = Lmap.Top V_Or_Uninitialized.top

  let name = "Eval_Offsm.Default_offsetmap"
end

(** This domain ignores initialization and danglingness alarms entirely.
    During pretty-printing, we skip them altogether.
    (In fact, it should be possible to prove inductively that everything
    is initialized except Top, because no computation introduces initialized
    bits, and nothing is initially uninitialized. *)
module V_Or_Uninitialized = struct
  include Cvalue.V_Or_Uninitialized

  let pretty_typ typ fmt v =
    let v = get_v v in
    if Cvalue.V.is_bottom v then Format.pp_print_string fmt "INDET"
    else pretty_typ typ fmt (initialized v)

  let pretty fmt v = pretty_typ None fmt v
end

module V_Offsetmap = struct
  include Cvalue.V_Offsetmap

  let pretty_generic ?typ ?pretty_v ?skip_v ?sep () fmt t =
    let pretty_v = Option.value ~default:V_Or_Uninitialized.pretty_typ pretty_v in
    pretty_generic ?typ ~pretty_v ?skip_v ?sep () fmt t
end

module Memory = struct
  include
    Lmap.Make_LOffset(V_Or_Uninitialized)(V_Offsetmap)(Default_offsetmap)

  let widen kf stmt s1 s2 =
    let wh = Widen.getWidenHints kf stmt in
    widen wh s1 s2

  let narrow x _y = `Value x
end


module D : Abstract_domain.Leaf
  with type state = Memory.t
   and type value = offsm_or_top
   and type location = Precise_locs.precise_location
= struct
  type value = offsm_or_top
  type state = Memory.t
  type location = Precise_locs.precise_location
  type origin

  include (Memory: sig
             include Datatype.S_with_collections with type t = state
             include Abstract_domain.Lattice with type state := state
           end)

  include Domain_builder.Complete (Memory)

  let log_category = dkey

  let empty _ = Memory.empty_map

  let enter_scope _kind _vars state = state (* default is Top, nothing to do *)
  let leave_scope _kf vars state =
    Memory.remove_variables vars state

  let kill loc state =
    Memory.add_binding ~exact:true state loc V_Or_Uninitialized.top

  let update _valuation st = `Value st (* TODO? *)

  let store loc state v =
    let state' =
      match v with
      | Top -> kill loc state
      | O o ->
        if not store_redundant && V_Offsetmap.is_single_interval o then
          kill loc state
        else
          match loc.Locations.size with
          | Int_Base.Top -> assert false
          | Int_Base.Value size ->
            Memory.paste_offsetmap
              ~from:o ~dst_loc:loc.Locations.loc ~size ~exact:true state
    in
    match state' with
    | Memory.Bottom -> `Bottom
    | _ -> `Value state'

  let generic_assign lv value state =
    let loc = Precise_locs.imprecise_location lv.lloc in
    let v = Eval.value_assigned value in
    let v = match v with
      | `Value v -> v
      (* Copy of fully indeterminate bits. We could store an uninitialized
         bottom, or something like that. Since this would be redundant
         with the legacy domain, we just drop the value. *)
      | `Bottom -> Top
    in
    store loc state v

  let assign _kinstr lv _e assignment _valuation state =
    generic_assign lv assignment state

  let assume _ _ _ _ state = `Value state

  let finalize_call _stmt _call _recursion ~pre:_ ~post = `Value post

  let start_recursive_call recursion state =
    let vars = List.map fst recursion.substitution @ recursion.withdrawal in
    Memory.remove_variables vars state

  let start_call _stmt _call recursion valuation state =
    update valuation state >>-: fun state ->
    Extlib.opt_fold start_recursive_call recursion state

  let extract_expr ~oracle:_ _context _state _exp =
    `Value (Offsm_value.Offsm.top, None), Alarmset.all

  (* Basic 'find' on a location *)
  let find_loc state loc =
    let size = Int_Base.project loc.Locations.size in
    let o = Memory.copy_offsetmap loc.Locations.loc size state in
    o >>-: fun o ->
    if Default_offsetmap.is_top o ||
       (not store_redundant && V_Offsetmap.is_single_interval o)
    then Offsm_value.Offsm.top
    else O o

  let extract_lval ~oracle:_ _context state _lv typ locs =
    let o =
      if Cil.typeHasQualifier "volatile" typ ||
         not (Cil.isArithmeticOrPointerType typ)
      then
        `Value (Top, None)
      else
        try
          let aux_loc loc o =
            let o' = find_loc state loc in
            Bottom.join Offsm_value.Offsm.join o o'
          in
          Precise_locs.fold aux_loc locs `Bottom >>-: fun v ->
          v, None
        with Abstract_interp.Error_Top -> `Value (Top, None)
    in
    o, Alarmset.all

  (* Memexec *)
  let relate _kf _bases _state = Base.SetLattice.empty
  let filter _kf _kind bases state =
    Memory.filter_by_shape bases state

  let reuse _kf bases ~current_input:input ~previous_output:output =
    let input =
      Memory.filter_base (fun b -> not (Base.Hptset.mem b bases)) input
    in
    let state =
      match output with
      | Memory.Bottom | Memory.Top as state -> state
      | Memory.Map outputs ->
        Memory.fold Memory.add_base outputs input
    in
    state

  (* Initial state *)
  let initialize_variable_using_type _ _ state = state
  let initialize_variable _ _ ~initialized:_ _ state = state

  (* Logic *)
  let logic_assign _assign location state =
    let loc = Precise_locs.imprecise_location location in
    kill loc state
end
