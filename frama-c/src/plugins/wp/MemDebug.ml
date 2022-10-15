(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

open Cil_datatype
open Lang.F
open Sigs

(* ------------------------------------------------------------------------ *)
(* ----  Pretty-printers                                               ---- *)
(* ------------------------------------------------------------------------ *)

let pp_sequence pp_val fmt seq =
  Format.fprintf fmt "@[{pre=%a,@,post=%a}@]"
    pp_val seq.pre pp_val seq.post

let pp_equation fmt = function
  | Set (lt, rt) -> Format.fprintf fmt "@[%a =@, %a@]" pp_term lt pp_term rt
  | Assert pred -> pp_pred fmt pred

let pp_acs fmt = function
  | RW -> Format.pp_print_string fmt "RW"
  | RD -> Format.pp_print_string fmt "RD"
  | OBJ -> Format.pp_print_string fmt "OBJ"

let pp_value pp_loc fmt = function
  | Val t -> pp_term fmt t
  | Loc l -> pp_loc fmt l

let pp_rloc pp_loc fmt = function
  | Rloc(_obj,l) -> Format.fprintf fmt "[@{%a}@]" pp_loc l
  | Rrange(l,_obj,tmin,tmax) ->
    Format.fprintf fmt "@[%a+(%a..%a)@]" pp_loc l
      (Pretty_utils.pp_opt pp_term) tmin (Pretty_utils.pp_opt pp_term) tmax

let pp_sloc pp_loc fmt = function
  | Sloc l -> Format.fprintf fmt "@[{%a}@]" pp_loc l
  | Sarray(l,_obj,size) -> Format.fprintf fmt "@[%a+(0..%d)@]" pp_loc l size
  | Srange(l,_obj,tmin,tmax) ->
    Format.fprintf fmt "@[%a+(%a..%a)@]" pp_loc l
      (Pretty_utils.pp_opt pp_term) tmin (Pretty_utils.pp_opt pp_term) tmax
  | Sdescr(xs,l,p) ->
    Format.fprintf fmt "@[{ %a @,| %a@,; %a }@]" pp_loc l
      (Pretty_utils.pp_list pp_var) xs pp_pred p

(* ------------------------------------------------------------------------ *)
(* ---- Debug Memory Model                                             ---- *)
(* ------------------------------------------------------------------------ *)

let dkey_cons   = Wp_parameters.register_category "memdebug:cons"
let dkey_loc    = Wp_parameters.register_category "memdebug:loc"
let dkey_cast   = Wp_parameters.register_category "memdebug:cast"
let dkey_access = Wp_parameters.register_category "memdebug:access"
let dkey_valid  = Wp_parameters.register_category "memdebug:valid"
let dkey_alias  = Wp_parameters.register_category "memdebug:alias"

let debug_cons = Wp_parameters.debug ~dkey:dkey_cons
let debug_loc = Wp_parameters.debug ~dkey:dkey_loc
let debug_cast = Wp_parameters.debug ~dkey:dkey_cast
let debug_access = Wp_parameters.debug ~dkey:dkey_access
let debug_valid = Wp_parameters.debug ~dkey:dkey_valid
let debug_alias = Wp_parameters.debug ~dkey:dkey_alias

module Make(M : Sigs.Model) =
struct
  let datatype = "MemDebug." ^ M.datatype
  let configure = M.configure

  let hypotheses = M.hypotheses

  module Chunk = M.Chunk

  module Heap = M.Heap
  module Sigma = M.Sigma

  type loc = M.loc
  type chunk = M.chunk
  type sigma = M.sigma
  type segment = M.segment
  type state = M.state

  (* ---------------------------------------------------------------------- *)
  (* ----  Pretty-printing                                             ---- *)
  (* ---------------------------------------------------------------------- *)

  let pretty = M.pretty

  let state = M.state
  let iter = M.iter
  let lookup = M.lookup
  let updates = M.updates
  let apply = M.apply

  let vars = M.vars
  let occurs = M.occurs

  (* ---------------------------------------------------------------------- *)
  (* ----  Constructors                                               ----- *)
  (* ---------------------------------------------------------------------- *)

  let null =
    let l = M.null in debug_cons "null:@, %a" pretty l;
    M.null

  let literal ~eid cstr =
    let l = M.literal ~eid cstr in
    debug_cons "literal ~eid:%d ->@, %a" eid pretty l;
    l

  let cvar x =
    let l = M.cvar x in
    debug_cons "cvar %a ->@, %a" Varinfo.pretty x pretty l;
    l

  let pointer_loc e =
    let l = M.pointer_loc e in
    debug_cons "term2loc %a ->@, %a" pp_term e pretty l;
    l
  let pointer_val l =
    let e = M.pointer_val l in
    debug_cons "loc2term %a ->@, %a" pretty l pp_term e;
    e

  (* ---------------------------------------------------------------------- *)
  (* ----  Operations                                                  ---- *)
  (* ---------------------------------------------------------------------- *)

  let field l fd =
    let l' = M.field l fd in
    debug_loc "@[%a.%a ->@, %a@]" pretty l Fieldinfo.pretty fd pretty l';
    l'
  let shift l obj e =
    let l' = M.shift l obj e in
    debug_loc "@[%a+%a ->@, %a@]" pretty l pp_term e pretty l';
    l'

  let base_addr l =
    let l' = M.base_addr l in
    debug_loc "@[base_addr: %a -> %a@]" pretty l pretty l';
    l'

  let block_length = M.block_length

  (* ---------------------------------------------------------------------- *)
  (* ----  Casting                                                    ----- *)
  (* ---------------------------------------------------------------------- *)

  let cast ty l =
    let l' = M.cast ty l in
    debug_cast "(%a)%a -> %a" Ctypes.pretty ty.post pretty l pretty l';
    l'

  let loc_of_int obj e =
    let l = M.loc_of_int obj e in
    debug_cast "(%a)%a -> %a" Ctypes.pretty obj pp_term e pretty l;
    l
  let int_of_loc cint l =
    let e = M.int_of_loc cint l in
    debug_cast "(%a)%a -> %a" Ctypes.pp_int cint pretty l pp_term e;
    e

  (* ---------------------------------------------------------------------- *)
  (* ----  Domain                                                     ----- *)
  (* ---------------------------------------------------------------------- *)

  let domain = M.domain

  (* ---------------------------------------------------------------------- *)
  (* ----  Memory Access                                              ----- *)
  (* ---------------------------------------------------------------------- *)

  let load s obj l =
    let v = M.load s obj l in
    debug_access "@[load %a @, %a @, %a ->@, %a@]@."
      Sigma.pretty s Ctypes.pretty obj pretty l (pp_value pretty) v;
    v

  let load_init _s _obj _l = e_false

  let stored seq obj l t =
    let preds = M.stored seq obj l t in
    debug_access "@[stored %a@, %a@, %a@, %a ->@, %a@]@."
      (pp_sequence Sigma.pretty) seq Ctypes.pretty obj pretty l pp_term t
      (Pretty_utils.pp_list pp_equation) preds;
    preds

  let stored_init _seq _obj _l _v = []

  let copied seq obj ll rl =
    let preds = M.copied seq obj ll rl in
    debug_access "@[copied %a@, %a@, %a@, %a ->@, %a@]@."
      (pp_sequence Sigma.pretty) seq Ctypes.pretty obj pretty ll pretty rl
      (Pretty_utils.pp_list pp_equation) preds;
    preds

  let copied_init _seq _obj _ll _rl = []

  let assigned seq obj sloc =
    let preds = M.assigned seq obj sloc in
    debug_access "@[assigned %a@, %a@, %a ->@, %a@]@."
      (pp_sequence Sigma.pretty) seq Ctypes.pretty obj (pp_sloc pretty) sloc
      (Pretty_utils.pp_list pp_equation) preds;
    preds

  (* ---------------------------------------------------------------------- *)
  (* ----  Pointer Comparison                                         ----- *)
  (* ---------------------------------------------------------------------- *)

  let is_null = M.is_null
  let loc_eq = M.loc_eq
  let loc_lt = M.loc_lt
  let loc_leq = M.loc_leq
  let loc_neq = M.loc_neq
  let loc_diff = M.loc_diff

  (* ---------------------------------------------------------------------- *)
  (* ----  Validity                                                   ----- *)
  (* ---------------------------------------------------------------------- *)

  let valid s acs seg =
    let p = M.valid s acs seg in
    debug_valid "@[valid %a@, %a@, %a ->@, %a@]@."
      Sigma.pretty s pp_acs acs (pp_rloc pretty) seg pp_pred p;
    p

  let invalid s seg =
    let p = M.invalid s seg in
    debug_valid "@[invalid %a@, %a ->@, %a@]@."
      Sigma.pretty s (pp_rloc pretty) seg pp_pred p;
    p

  let scope = M.scope
  let global = M.global

  (* ---------------------------------------------------------------------- *)
  (* ----  Separation                                                 ----- *)
  (* ---------------------------------------------------------------------- *)

  let included seg1 seg2 =
    let p = M.included seg1 seg2 in
    debug_alias "@[included %a@, %a ->@, %a@]@."
      (pp_rloc pretty) seg1 (pp_rloc pretty) seg2 pp_pred p;
    p

  let separated seg1 seg2 =
    let p = M.separated seg1 seg2 in
    debug_alias "@[separated %a@, %a ->@, %a@]@."
      (pp_rloc pretty) seg1 (pp_rloc pretty) seg2 pp_pred p;
    p


  (** todo *)
  let initialized = M.initialized
  let alloc = M.alloc
  let frame = M.frame
  let is_well_formed = M.is_well_formed
  let base_offset = M.base_offset
  type domain = M.domain
  let configure_ia = M.configure_ia

end
