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

open Cil_types
open Cil
open Abstract_interp

type variable_validity = {
  mutable weak: bool;
  mutable min_alloc : Int.t;
  mutable max_alloc : Int.t;
  max_allocable: Int.t (* not mutable, determined when the base is created *);
}

type validity =
  | Empty
  | Known of Int.t * Int.t
  | Unknown of Int.t * Int.t option * Int.t
  | Variable of variable_validity
  | Invalid

let pretty_validity fmt v =
  match v with
  | Empty -> Format.fprintf fmt "Empty"
  | Unknown (b,k,e)  ->
    Format.fprintf fmt "Unknown %a/%a/%a"
      Int.pretty b (Pretty_utils.pp_opt Int.pretty) k Int.pretty e
  | Known (b,e)  -> Format.fprintf fmt "Known %a-%a" Int.pretty b Int.pretty e
  | Invalid -> Format.fprintf fmt "Invalid"
  | Variable variable_v ->
    Format.fprintf fmt "Variable [0..%a--%a]"
      Int.pretty variable_v.min_alloc Int.pretty variable_v.max_alloc

module Validity = Datatype.Make
    (struct
      type t = validity
      let name = "Base.validity"
      let structural_descr = Structural_descr.t_abstract
      let reprs = [ Known (Int.zero, Int.one) ]

      (* Invalid > Variable > Unknown > Known > Empty *)
      let compare v1 v2 = match v1, v2 with
        | Empty, Empty -> 0
        | Known (b1, e1), Known (b2, e2) ->
          let c = Int.compare b1 b2 in
          if c = 0 then Int.compare e1 e2 else c
        | Unknown (b1, m1, e1), Unknown (b2, m2, e2) ->
          let c = Int.compare b1 b2 in
          if c = 0 then
            let c = Option.compare Int.compare m1 m2 in
            if c = 0 then Int.compare e1 e2 else c
          else c
        | Variable v1, Variable v2 ->
          let c = Int.compare v1.min_alloc v2.min_alloc in
          if c = 0 then
            let c = Int.compare v1.max_alloc v2.max_alloc in
            if c = 0 then Int.compare v1.max_allocable v2.max_allocable
            else c
          else c
        | Invalid, Invalid -> 0
        | Empty, (Known _ | Unknown _ | Variable _ | Invalid)
        | Known _, (Unknown _ | Variable _ | Invalid)
        | Unknown _, (Variable _ | Invalid)
        | Variable _, Invalid -> -1
        | Invalid, (Variable _ | Unknown _ | Known _ | Empty)
        | Variable _, (Unknown _ | Known _ | Empty)
        | Unknown _, (Known _ | Empty)
        | Known _, Empty -> 1

      let equal = Datatype.from_compare

      let hash v = match v with
        | Empty -> 13
        | Invalid -> 37
        | Known (b, e) -> Hashtbl.hash (3, Int.hash b, Int.hash e)
        | Unknown (b, m, e) ->
          Hashtbl.hash (7, Int.hash b, Extlib.opt_hash Int.hash m, Int.hash e)
        | Variable variable_v ->
          Hashtbl.hash (Int.hash variable_v.min_alloc, Int.hash variable_v.max_alloc)

      let pretty = pretty_validity
      let mem_project = Datatype.never_any_project
      let internal_pretty_code = Datatype.pp_fail
      let rehash = Datatype.identity
      let copy (x:t) = x
      let varname _ = "v"
    end)

type cstring = CSString of string | CSWstring of Escape.wstring

type deallocation = Malloc | VLA | Alloca

type base =
  | Var of varinfo * validity
  | CLogic_Var of logic_var * typ * validity
  | Null (** base for addresses like [(int* )0x123] *)
  | String of int * cstring (** String constants *)
  | Allocated of varinfo * deallocation * validity

let id = function
  | Var (vi,_) | Allocated (vi,_,_) -> vi.vid
  | CLogic_Var (lvi, _, _) -> lvi.lv_id
  | Null -> 0
  | String (id,_) -> id

let hash = id

let null = Null

let is_null x = match x with Null -> true | _ -> false

let pretty fmt t =
  match t with
  | String (_, CSString s) -> Format.fprintf fmt "%S" s
  | String (_, CSWstring s) ->
    Format.fprintf fmt "L\"%s\"" (Escape.escape_wstring s)
  | Var (t,_) | Allocated (t,_,_) -> Printer.pp_varinfo fmt t
  | CLogic_Var (lvi, _, _) -> Printer.pp_logic_var fmt lvi
  | Null -> Format.pp_print_string fmt "NULL"

let pretty_addr fmt t =
  (match t with
   | Var _ | CLogic_Var _ | Allocated _ ->
     Format.pp_print_string fmt "&"
   | String _ | Null -> ()
  );
  pretty fmt t

let compare v1 v2 = Datatype.Int.compare (id v1) (id v2)

let typeof v =
  match v with
  | String (_,_) -> Some charConstPtrType
  | CLogic_Var (_, ty, _) -> Some ty
  | Null -> None
  | Var (v,_) | Allocated(v,_,_) -> Some (unrollType v.vtype)

let cstring_bitlength s =
  let u, l =
    match s with
    | CSString s ->
      bitsSizeOf charType, (String.length s)
    | CSWstring s ->
      bitsSizeOf theMachine.wcharType, (List.length s)
  in
  Int.of_int (u*(succ l))

let bits_sizeof v =
  match v with
  | String (_,e) ->
    Int_Base.inject (cstring_bitlength e)
  | Null -> Int_Base.top
  | Var (v,_) | Allocated (v,_,_) ->
    Bit_utils.sizeof_vid v
  | CLogic_Var (_, ty, _) -> Bit_utils.sizeof ty

let dep_absolute = [Kernel.AbsoluteValidRange.self]

module MinValidAbsoluteAddress =
  State_builder.Ref
    (Abstract_interp.Int)
    (struct
      let name = "MinValidAbsoluteAddress"
      let dependencies = dep_absolute
      let default () = Abstract_interp.Int.zero
    end)

module MaxValidAbsoluteAddress =
  State_builder.Ref
    (Abstract_interp.Int)
    (struct
      let name = "MaxValidAbsoluteAddress"
      let dependencies = dep_absolute
      let default () = Abstract_interp.Int.minus_one
    end)

let () =
  Kernel.AbsoluteValidRange.add_set_hook
    (fun _ x ->
       try Scanf.sscanf x "%s@-%s"
             (fun min max ->
                (* let mul_CHAR_BIT = Int64.mul (Int64.of_int (bitsSizeOf charType)) in *)
                (* the above is what we would like to write but it is too early *)
                let mul_CHAR_BIT = Int.mul Int.eight in
                MinValidAbsoluteAddress.set
                  (mul_CHAR_BIT (Int.of_string min));
                MaxValidAbsoluteAddress.set
                  ((Int.pred (mul_CHAR_BIT (Int.succ (Int.of_string max))))))
       with End_of_file | Scanf.Scan_failure _ | Failure _
          | Invalid_argument _ as e ->
         Kernel.abort "Invalid -absolute-valid-range integer-integer: each integer may be in decimal, hexadecimal (0x, 0X), octal (0o) or binary (0b) notation and has to hold in 64 bits. A correct example is -absolute-valid-range 1-0xFFFFFF0.@\nError was %S@."
           (Printexc.to_string e))

let min_valid_absolute_address = MinValidAbsoluteAddress.get
let max_valid_absolute_address = MaxValidAbsoluteAddress.get

let validity_from_size size =
  assert Int.(ge size zero);
  if Int.(equal size zero) then Empty
  else Known (Int.zero, Int.pred size)

let validity_from_known_size size =
  match size with
  | Int_Base.Value size ->
    (* all start to be valid at offset 0 *)
    validity_from_size size
  | Int_Base.Top ->
    Unknown (Int.zero, None, Bit_utils.max_bit_address ())

let validity b =
  match b with
  | Var (_,v) | CLogic_Var (_, _, v) | Allocated (_,_,v) -> v
  | Null ->
    let mn = min_valid_absolute_address ()in
    let mx = max_valid_absolute_address () in
    if Integer.gt mx mn then
      Known (mn, mx)
    else
      Invalid
  | String _ ->
    let size = bits_sizeof b in
    validity_from_known_size size

let is_read_only base =
  match base with
  | String _ -> true
  | Var (v,_) -> typeHasQualifier "const" v.vtype
  | _ -> false

(* Minor optimization compared to [is_weak (validity b)] *)
let is_weak = function
  | Allocated (_, _, Variable { weak }) -> weak
  | _ -> false

(* Does a C type end by an empty struct? *)
let rec final_empty_struct = function
  | TArray (typ, _, _) -> final_empty_struct typ
  | TComp (compinfo, _) ->
    begin
      match compinfo.cfields with
      | Some [] | None -> true
      | Some l ->
        let last_field = List.(hd (rev l)) in
        try Cil.bitsSizeOf last_field.ftype = 0
        with Cil.SizeOfError _ -> false
    end
  | TNamed (typeinfo, _) -> final_empty_struct typeinfo.ttype
  | TVoid _ | TInt _ | TFloat _ | TPtr _ | TEnum _
  | TFun _ | TBuiltin_va_list _ -> false

(* Does a base end by an empty struct? *)
let final_empty_struct = function
  | Var (vi, _) | Allocated (vi, _, _) -> final_empty_struct vi.vtype
  | _ -> false

type access = Read of Integer.t | Write of Integer.t | No_access
let for_writing = function Write _ -> true | Read _ | No_access -> false

let is_empty = function
  | Read size | Write size -> Int.(equal zero size)
  | No_access -> true

(* Computes the last valid offset for an access of the base [base] with [max]
   valid bits: [max - size + 1] for an access of size [size]. *)
let last_valid_offset base max = function
  | Read size | Write size ->
    if Int.is_zero size
    (* For an access of size 0, [max] is the last valid offset, unless the base
       ends by an empty struct, in which case [max+1] is also a valid offset. *)
    then if final_empty_struct base then Int.succ max else max
    else Int.sub max (Int.pred size)
  | No_access -> Int.succ max (* A pointer can point just beyond its object. *)

let offset_for_validity ~bitfield access base =
  match validity base with
  | Empty -> if is_empty access then Ival.zero else Ival.bottom
  | Invalid -> if access = No_access then Ival.zero else Ival.bottom
  | Known (min, max) | Unknown (min, _, max) ->
    let max = last_valid_offset base max access in
    if bitfield
    then Ival.inject_range (Some min) (Some max)
    else
      Ival.inject_interval ~min:(Some min) ~max:(Some max) ~rem:Int.zero
        ~modu:Int.eight
  | Variable variable_v ->
    let maxv = last_valid_offset base variable_v.max_alloc access in
    Ival.inject_range (Some Int.zero) (Some maxv)

let valid_offset ?(bitfield=true) access base =
  if for_writing access && is_read_only base
  then Ival.bottom
  else
    let offset = offset_for_validity ~bitfield access base in
    (* When -absolute-valid-range is enabled, the Null base has a Known validity
       that does not include 0. In this case, adds 0 as possible offset for a
       pointer without memory access. *)
    if access = No_access && is_null base
    then Ival.(join zero offset)
    else offset

let offset_is_in_validity access base ival =
  let is_valid_for_bounds min_bound max_bound =
    match Ival.min_and_max ival with
    | Some min, Some max ->
      Int.ge min min_bound &&
      Int.le max (last_valid_offset base max_bound access)
    | _, _ -> false
  in
  match validity base with
  | Empty -> is_empty access && Ival.(equal zero ival)
  | Invalid -> access = No_access && Ival.(equal zero ival)
  | Known (min, max)
  | Unknown (min, Some max, _) -> is_valid_for_bounds min max
  | Unknown (_, None, _) -> false (* All accesses are possibly invalid. *)
  | Variable v -> is_valid_for_bounds Int.zero v.min_alloc

let is_valid_offset access base offset =
  Ival.is_bottom offset
  || not (for_writing access && (is_read_only base))
     && (offset_is_in_validity access base offset
         || access = No_access && is_null base && Ival.(equal zero offset))

let is_function base =
  match base with
  | String _ | Null | CLogic_Var _ | Allocated _ -> false
  | Var(v,_) ->
    isFunctionType v.vtype

let equal v w = (id v) = (id w)

let is_aligned_by b alignment =
  if Int.is_zero alignment
  then false
  else
    try
      match b with
      | Var (v,_) | Allocated(v,_,_) ->
        Int.is_zero (Int.e_rem (Int.of_int (Cil.bytesAlignOf v.vtype)) alignment)
      | CLogic_Var (_, ty, _) ->
        Int.is_zero (Int.e_rem (Int.of_int (Cil.bytesAlignOf ty)) alignment)
      | Null -> true
      | String _ -> Int.is_one alignment
    with Cil.SizeOfError _ -> false

let is_any_formal_or_local v =
  match v with
  | Var (v,_) -> v.vsource && not v.vglob
  | Allocated _ | CLogic_Var _ -> false
  | Null | String _ -> false

let is_any_local v =
  match v with
  | Var (v,_) -> v.vsource && not v.vglob && not v.vformal
  | Allocated _ | CLogic_Var _ -> false
  | Null | String _ -> false

let is_global v =
  match v with
  | Var (v,_) -> v.vglob
  | Allocated _ | Null | String _ -> true
  | CLogic_Var _ -> false

let is_formal_or_local v fundec =
  match v with
  | Var (v,_) -> Ast_info.Function.is_formal_or_local v fundec
  | Allocated _ | CLogic_Var _ | Null | String _ -> false

let is_formal_of_prototype v vi =
  match v with
  | Var (v,_) -> Ast_info.Function.is_formal_of_prototype v vi
  | Allocated _ | CLogic_Var _ | Null | String _ -> false

let is_local v fundec =
  match v with
  | Var (v,_) -> Ast_info.Function.is_local v fundec
  | Allocated _ | CLogic_Var _ | Null | String _ -> false

let is_formal v fundec =
  match v with
  | Var (v,_)  -> Ast_info.Function.is_formal v fundec
  | Allocated _ | CLogic_Var _ | Null | String _ -> false

let is_block_local v block =
  match v with
  | Var (v,_) -> Ast_info.is_block_local v block
  | Allocated _ | CLogic_Var _ | Null | String _ -> false

let validity_from_type v =
  if isFunctionType v.vtype then Invalid
  else
    let max_valid = Bit_utils.sizeof_vid v in
    match max_valid with
    | Int_Base.Top ->
      Unknown (Int.zero, None, Bit_utils.max_bit_address ())
    | Int_Base.Value size -> validity_from_size size

type range_validity =
  | Invalid_range
  | Valid_range of Int_Intervals_sig.itv option

let valid_range = function
  | Invalid -> Invalid_range
  | Empty -> Valid_range None
  | Known (min_valid,max_valid)
  | Unknown (min_valid,_,max_valid)-> Valid_range (Some (min_valid, max_valid))
  | Variable variable_v -> Valid_range (Some (Int.zero, variable_v.max_alloc))

let is_weak_validity = function
  | Variable { weak } -> weak
  | _ -> false

let create_variable_validity ~weak ~min_alloc ~max_alloc =
  let max_allocable = Bit_utils.max_bit_address () in
  { weak; min_alloc; max_alloc; max_allocable }

let update_variable_validity v ~weak ~min_alloc ~max_alloc =
  v.min_alloc <- Int.min min_alloc v.min_alloc;
  v.max_alloc <- Int.max max_alloc v.max_alloc;
  if weak then v.weak <- true


module Base = struct
  include Datatype.Make_with_collections
      (struct
        type t = base
        let name = "Base"
        let structural_descr = Structural_descr.t_abstract (* TODO better *)
        let reprs = [ Null ]
        let equal = equal
        let compare = compare
        let pretty = pretty
        let hash = hash
        let mem_project = Datatype.never_any_project
        let internal_pretty_code = Datatype.pp_fail
        let rehash = Datatype.identity
        let copy = Datatype.undefined
        let varname = Datatype.undefined
      end)
  let id = id
  let pretty_debug = pretty
end

include Base

module Hptshape = Hptmap.Shape (Base)

module Hptset = Hptset.Make
    (Base)
    (struct let v = [ [ ]; [Null] ] end)
    (struct let l = [ Ast.self ] end)
let () = Ast.add_monotonic_state Hptset.self
let () = Ast.add_hook_on_update Hptset.clear_caches

let null_set = Hptset.singleton Null

module VarinfoNotSource =
  Cil_state_builder.Varinfo_hashtbl
    (Base)
    (struct
      let name = "Base.VarinfoLogic"
      let dependencies = [ Ast.self ]
      let size = 89
    end)
let () = Ast.add_monotonic_state VarinfoNotSource.self

let base_of_varinfo varinfo =
  assert varinfo.vsource;
  let validity = validity_from_type varinfo in
  Var (varinfo, validity)

module Validities =
  Cil_state_builder.Varinfo_hashtbl
    (Base)
    (struct
      let name = "Base.Validities"
      let dependencies = [ Ast.self ]
      (* No dependency on Kernel.AbsoluteValidRange.self needed:
         the null base is not present in this table (not a varinfo) *)
      let size = 117
    end)
let () = Ast.add_monotonic_state Validities.self

let of_varinfo_aux = Validities.memo base_of_varinfo

let register_memory_var varinfo validity =
  assert (not varinfo.vsource && not (VarinfoNotSource.mem varinfo));
  let base = Var (varinfo,validity) in
  VarinfoNotSource.add varinfo base;
  base

let register_allocated_var varinfo deallocation validity =
  assert (not varinfo.vsource);
  let base = Allocated (varinfo,deallocation,validity) in
  VarinfoNotSource.add varinfo base;
  base

let of_c_logic_var lv =
  match Logic_utils.unroll_type lv.lv_type with
  | Ctype ty ->
    CLogic_Var (lv, ty, validity_from_known_size (Bit_utils.sizeof ty))
  | _ -> Kernel.fatal "Logic variable with a non-C type %s" lv.lv_name

let of_varinfo varinfo =
  if varinfo.vsource
  then of_varinfo_aux varinfo
  else
    try VarinfoNotSource.find varinfo
    with Not_found ->
      Kernel.fatal "Querying base for unknown non-source variable %a"
        Printer.pp_varinfo varinfo

exception Not_a_C_variable

let to_varinfo t = match t with
  | Var (t,_) | Allocated (t,_,_) -> t
  | CLogic_Var _ | Null | String _ -> raise Not_a_C_variable


module LiteralStrings =
  State_builder.Hashtbl
    (Datatype.Int.Hashtbl)
    (Base)
    (struct
      let name = "literal strings"
      let dependencies = [ Ast.self ]
      let size = 17
    end)
let () = Ast.add_monotonic_state LiteralStrings.self

let of_string_exp e =
  let cstring = match e.enode with
    | Const (CStr s) -> CSString s
    | Const (CWStr s) -> CSWstring s
    | _ -> assert false
  in
  LiteralStrings.memo (fun _ -> String (Cil_const.new_raw_id (), cstring)) e.eid

module SetLattice = Make_Hashconsed_Lattice_Set(Base)(Hptset)

module BMap =
  Hptmap.Make (Base) (Base) (Hptmap.Comp_unused)
    (struct let v = [ [] ] end)
    (struct let l = [ Ast.self ] end)

type substitution = base Hptshape.map

let substitution_from_list list =
  let add map (key, elt) = BMap.add key elt map in
  List.fold_left add BMap.empty list

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
