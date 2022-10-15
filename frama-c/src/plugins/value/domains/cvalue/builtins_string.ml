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

module Comp = Abstract_interp.Comp

(* Definition of a search. *)
type kind =
  { search: Ival.t;         (* Set of possible characters searched. *)
    stop_at_0: bool;        (* Does the search stop when encountering \0. *)
    size: Integer.t;        (* Size in bits of a character. *)
    signed: bool;           (* Whether the characters are signed. *)
    limit: Ival.t option; } (* Limit in bits of the search. *)

(* Result of a search. We always compute in bits both the offset and the length.
   The null field is true if the search may end normally but empty-handed. *)
type t =
  { null: bool;     (* Is null a possible resulting pointer? *)
    offset: Ival.t; (* Offsets of the found characters. *)
    length: Ival.t; (* Distance between [offset] and the start of the search. *)
    alarm: bool; }  (* True if possible undefined behavior. *)

let empty =
  { null = false; offset = Ival.bottom; length = Ival.bottom; alarm = false }
let join a b =
  { null = a.null || b.null;
    offset = Ival.join a.offset b.offset;
    length = Ival.join a.length b.length;
    alarm = a.alarm || b.alarm }

(* Accumulator propagated through a search in an offsetmap. *)
type acc =
  { read: t;       (* The result of the search. *)
    from: Ival.t;  (* The offsets from which the current search has begun. *)
    stop: bool; }  (* True if the search is completely done. *)

let the_max_int ival = Option.get (Ival.max_int ival)

let pos_min_int ival =
  match Ival.min_int ival with
  | None -> Integer.zero
  | Some i -> Integer.(max zero i)

let make_interval ~min ~max =
  Ival.inject_interval ~min:(Some min) ~max:(Some max)

(* Backward reduction of an ival against an integer.*)
let backward_comp_left comp ival integer =
  Ival.backward_comp_int_left comp ival (Ival.inject_singleton integer)

(* The search stops at [offset]. If the search always starts before [offset],
   the search is stopped. Otherwise, the search continues beyond [offset], but
   we reduce [from] to remove offsets before [offset]; this improves the
   precision of the computed length. This reduction assumes that all the reads
   at [offset] are consecutive. *)
let break ~offset ~from read =
  let from = backward_comp_left Comp.Gt from (the_max_int offset) in
  { read; from; stop = Ival.is_bottom from }

(* Computes the precise offset and length when reading exactly the searched
   character at [offset]. The offset can be reduced to the first offset beyond
   the last offset in which the search may start. The maximal length is the
   length for the first offset or the period of [offset]. *)
let read_exact_char ~offset ~from =
  let min = Integer.max (the_max_int from) (pos_min_int offset) in
  let offset = backward_comp_left Comp.Le offset min in
  let length = Ival.sub_int offset from in
  if not (Ival.is_singleton_int offset)
  then
    let _, _, _, modu = Ival.min_max_r_mod offset in
    let start_length = Integer.sub (pos_min_int offset) (pos_min_int from) in
    let max_length = Integer.max start_length modu in
    let length = backward_comp_left Comp.Lt length max_length in
    offset, length
  else offset, length

(* Checks if some limits are reached after a read at [offset]. In this case,
   adds these limits as possible lengths in [t], and adds null to [t]. *)
let check_limit kind ~offset ~from t =
  match kind.limit with
  | None -> t
  | Some limit ->
    let offset = Ival.add_singleton_int kind.size offset in
    let length = Ival.sub_int offset from in
    let limit_reached = Ival.backward_comp_int_left Comp.Le limit length in
    if Ival.is_bottom limit_reached then t else
      let length = Ival.join t.length limit_reached in
      { t with null = true; length }

(* Reads the character [cvalue] at offsets [offset]. [kind] describes the
   search, [from] are the offsets from which the current search has begun,
   and is used to compute the length. The reduction of [from] assumes that
   the reads at [offset] are consecutive. *)
let read_one_char kind ~offset ~from cvalue =
  let alarm = Cvalue.V_Or_Uninitialized.is_indeterminate cvalue in
  let cvalue = Cvalue.V_Or_Uninitialized.get_v cvalue in
  (* If no value can be read here, break the search. *)
  if Cvalue.V.is_bottom cvalue
  then break ~offset ~from { empty with alarm }
  else
    let ival = Cvalue.V.project_ival cvalue in
    (* Casts the ival into the proper type. *)
    let size, signed = kind.size, kind.signed in
    let ival = Ival.reinterpret_as_int ~size ~signed ival in
    (* May the search reach a terminating character here? *)
    let null = kind.stop_at_0 && Ival.contains_zero ival in
    (* Compares [ival] with the searched characters. *)
    let read, found =
      if not (Ival.intersects ival kind.search)
      then { empty with null; alarm }, false
      else
        let exact = Ival.(equal ival kind.search && is_singleton_int ival) in
        let offset, length =
          if exact
          then read_exact_char ~offset ~from
          else offset, Ival.sub_int offset from
        in
        { null; offset; length; alarm }, exact
    in
    (* Breaks the search if it always reaches a searched or a terminating
       character here. Otherwise, checks if a limit has been reached. *)
    if found || (kind.stop_at_0 && Ival.is_zero ival)
    then break ~offset ~from read
    else
      let read = check_limit kind ~from ~offset read in
      { read; from; stop = false }

(* Reads the character [cvalue] at [offset], and updates [acc] accordingly.  *)
let read_char kind offset cvalue acc =
  let new_acc = read_one_char kind ~offset ~from:acc.from cvalue in
  { new_acc with read = join acc.read new_acc.read }

(* Searches the range [min..max] of the [offsetmap], that contains a repeated
   value of size [v_size]. *)
let search_offsetmap_range kind offsetmap validity ~min ~max ~v_size acc =
  let size = kind.size in
  (* Reads will repeat themselves every [modu] bits. *)
  let modu = Integer.ppcm v_size size in
  let max_reads = Integer.(to_int_exn (e_div modu size)) in
  (* Performs [max_reads] consecutive reads from offsets {[min] + k[modu]},
     bound by [max]. *)
  let search_until ~max acc =
    let rec read_index count ~min res =
      let rem = Integer.e_rem min modu in
      let offsets = make_interval ~min ~max ~rem ~modu in
      let cvalue = Cvalue.V_Offsetmap.find ~validity ~offsets ~size offsetmap in
      (* Be careful to not use this result [t] for the reads of the next
         characters, as the reduction of [acc.from] assumes that the reads at
         [offset] are consecutive, which is not the case here. Thus, we always
         read with the initial [acc], and accumulate the result in [res]. *)
      let t = read_char kind offsets cvalue acc in
      let read = join res.read t.read in
      (* At the end, all the reads are indeed consecutive, and we can
         use the narrow of the [from] for the next ranges of the offsetmap. *)
      let from = Ival.narrow res.from t.from in
      let res = { read; from; stop = res.stop || t.stop; } in
      let min = Integer.add min kind.size in
      if (Ival.is_singleton_int offsets && res.stop)
      || Integer.gt min max || count >= max_reads
      then res
      else read_index (count + 1) ~min res
    in
    read_index 1 ~min acc
  in
  (* The maximal offset we are sure to read from. *)
  let sure_offset = Integer.max min (the_max_int acc.from) in
  let sure_max = Integer.pred (Integer.add sure_offset modu) in
  (* If one of the read characters stops the search, the other characters will
     lead to imprecise results — as they are all periodic until [max]. Thus we
     perform a first read of the range until the maximal sure read offset. *)
  let acc =
    if Integer.lt sure_max max
    then search_until ~max:sure_max acc
    else acc
  in
  if acc.stop then acc else search_until ~max acc

(* Folds the [offsetmap] from [start] to [max]. *)
let fold_offsm kind ~validity ~start ~max ~rem offsetmap acc =
  let modu = kind.size in
  let process_range (start, max) (v, v_size, v_shift) acc =
    if acc.stop then acc else
      let min = Integer.round_up_to_r ~min:start ~r:rem ~modu in
      if Integer.gt min max then acc else
        let v_start = Abstract_interp.Rel.add_abs start v_shift in
        (* Only one read of the value is needed when:
           - the ending cut is aligned with the reads, meaning that no read
             overlaps between two ranges of the offsetmap.
           - and either the value is isotropic, or the repeated value has the
             same size than the reads. *)
        if Integer.equal rem (Integer.e_rem (Integer.succ max) modu) &&
           (Cvalue.V_Or_Uninitialized.is_isotropic v ||
            Integer.equal min v_start && Integer.equal v_size kind.size)
        then
          let offset = make_interval ~min ~max ~rem ~modu in
          read_char kind offset v acc
        else
          (* Otherwise, search the range by reading the offsetmap for each
             required offset. Less efficient, but equally precise. *)
          search_offsetmap_range kind offsetmap validity ~min ~max ~v_size acc
  in
  Cvalue.V_Offsetmap.fold_between
    ~entire:false (start, max) process_range offsetmap acc

(* Performs the search in the [offsetmap]. *)
let search_offsm kind ~validity ~offset ~rem offsetmap =
  let start = pos_min_int offset in
  (* Compute the maximal bit that can be read in the offsetmap. *)
  let base_max = match Base.valid_range validity with
    | Base.Invalid_range -> Integer.zero (* should not happen *)
    | Base.Valid_range None -> Bit_utils.max_bit_address ()
    | Base.Valid_range (Some (_min, max)) -> max
  in
  (* Uses [kind.limit] to bound the read. *)
  let limit_max = Option.bind kind.limit Ival.max_int in
  let max = match Ival.max_int offset, limit_max with
    | Some max_start, Some max_limit ->
      let max = Integer.(add max_start (pred max_limit)) in
      Integer.min base_max max
    | _, _ -> base_max
  in
  (* Starts the search with an empty accumulator. *)
  let acc = { read = empty; from = offset; stop = false } in
  let acc = fold_offsm kind ~validity ~start ~max ~rem offsetmap acc in
  (* Alarm if the search does not stop before the end of the offsetmap. *)
  if not acc.stop && Integer.gt (Integer.add max kind.size) base_max
  then { acc.read with alarm = true }
  else acc.read

(* Generic function to fold a search according to a small set of integers. *)
let search_by_folding ival search =
  if Ival.cardinal_is_less_than ival (Int_set.get_small_cardinal ())
  then Ival.fold_enum (fun ival acc -> join acc (search ival)) ival empty
  else search ival

(* Performs the search at offsets [offset] in the [base] offsetmap of [state].
   Folds the search according to the offset and the search characters, if they
   are small enough. *)
let search_base kind ~offset base state =
  let offsetmap = Cvalue.Model.find_base_or_default base state in
  match offsetmap with
  | `Bottom -> { empty with alarm = true }
  | `Top -> assert false
  | `Value offsetmap ->
    let validity = Base.validity base in
    let search_one_rem ~offset ~char ~rem acc =
      let kind = { kind with search = char } in
      let res = search_offsm kind ~validity ~offset ~rem offsetmap in
      join acc res
    in
    let search_one_char offset char =
      let rems = Ival.scale_rem ~pos:true kind.size offset in
      Ival.fold_int (fun rem -> search_one_rem ~offset ~char ~rem) rems empty
    in
    let search_one_offset offset =
      search_by_folding kind.search (search_one_char offset)
    in
    search_by_folding offset search_one_offset

(* Returns a map binding a result for each base of [str]. *)
let search_by_base kind str state =
  Locations.Location_Bits.fold_i
    (fun base offset acc ->
       let t = search_base kind ~offset base state in
       Base.Map.add base t acc)
    str Base.Map.empty

(* Computes a length from a map returned by [search_by_base]. [zero] is true
   if the limit may have been 0, in which case the length 0 is possible. *)
let return_length kind ~zero basemap =
  let positions = if zero then Ival.zero else Ival.bottom in
  let positions =
    Base.Map.fold (fun _ t acc -> Ival.join t.length acc) basemap positions
  in
  (* The computed length and the limit are expressed in bits. *)
  let positions = match kind.limit with
    | None -> positions
    | Some l -> Ival.backward_comp_int_left Comp.Le positions l
  in
  (* The returned length is expressed in number of characters. *)
  let positions = Ival.scale_div ~pos:false kind.size positions in
  let positions = Ival.backward_comp_int_left Comp.Ge positions Ival.zero in
  Cvalue.V.inject_ival positions

(* Computes a pointer to the characters found by [search_by_base]. Adds the null
   pointer if necessary. [zero] is true if the limit may have been 0. *)
let return_pointer ~zero basemap =
  let loc_bits =
    Base.Map.fold
      (fun base t acc -> Locations.Location_Bits.add base t.offset acc)
      basemap Locations.Location_Bits.bottom
  in
  let cvalue = Locations.loc_bits_to_loc_bytes loc_bits in
  if zero || Base.Map.exists (fun _base t -> t.null) basemap
  then Cvalue.V.add Base.null Ival.zero cvalue
  else cvalue

(* Returns a completely imprecise result, when the builtin fails. *)
let return_top ~length str =
  if length then Cvalue.V.top_int else
    let null = Cvalue.V.(add Base.null Ival.zero bottom) in
    Cvalue.V.fold_bases (fun b acc -> Cvalue.V.add b Ival.top acc) str null

(* The complete search. Returns the length if [length] is true, and a pointer
   to the found characters otherwise. Handles the case of a limit 0. *)
let search_char kind ~length state str =
  let basemap =
    if Option.fold ~some:Ival.is_zero ~none:false kind.limit
    then Base.Map.empty
    else search_by_base kind str state
  in
  let alarm = Base.Map.exists (fun _base t -> t.alarm) basemap in
  let zero = Option.fold ~some:Ival.contains_zero ~none:false kind.limit in
  if length
  then return_length kind ~zero basemap, alarm
  else return_pointer ~zero basemap, alarm

(* Reduces a pointer to a string to its valid part. Also returns a boolean
   indicating whether the pointer was completely valid or not. *)
let reduce_by_validity ~size cvalue =
  let loc_bits = Locations.loc_bytes_to_loc_bits cvalue in
  let loc = Locations.make_loc loc_bits (Int_Base.inject size) in
  if Locations.(is_valid Read loc)
  then
    let is_aligned _base ival =
      Ival.is_zero (Ival.scale_rem ~pos:true size ival)
    in
    let valid = Locations.Location_Bits.for_all is_aligned loc_bits in
    loc.Locations.loc, valid
  else
    let valid_loc = Locations.(valid_part Read ~bitfield:true loc) in
    valid_loc.Locations.loc, false

type char = Char | Wide

let bits_size = function
  | Char -> Integer.eight
  | Wide -> Integer.of_int (Cil.bitsSizeOf Cil.theMachine.Cil.wcharType)

let signed_char = function
  | Char -> not Cil.(theMachine.theMachine.Cil_types.char_is_unsigned)
  | Wide -> Cil.isSignedInteger Cil.theMachine.Cil.wcharType

(* Converts the searched characters into char; needed for strchr and memchr. *)
let searched_char ~size ~signed cvalue =
  let ival = Cvalue.V.project_ival cvalue in
  if size = Integer.eight
  then Ival.cast_int_to_int ~size ~signed ival
  else ival

(* Interprets the arguments [args], builds the [kind] and runs the search.
   [search] are the searched characters, unless it is bottom, in which case the
   searched characters are the second argument. [size] is the type of the
   characters. [stop_at_0] is true if the search stops unsuccessfully on
   character 0. [limit] indicates which argument contains the limit, if any.
   The resulting function is the one exported. *)
let do_search ~search ~stop_at_0 ~typ ~length ?limit = fun state args ->
  let size = bits_size typ in
  let signed = signed_char typ in
  let str = List.nth args 0 in
  try
    let str, valid = reduce_by_validity ~size str in
    let search =
      if Ival.is_bottom search
      then searched_char ~size ~signed (List.nth args 1)
      else search
    in
    (* When searching exactly 0, the search naturally stops at 0. *)
    let stop_at_0 = if Ival.is_zero search then false else stop_at_0 in
    let interpret_limit n =
      let cvalue = List.nth args n in
      let limit = Ival.scale size (Cvalue.V.project_ival cvalue) in
      Ival.(narrow positive_integers limit)
    in
    let limit = Option.map interpret_limit limit in
    let kind = { search; stop_at_0; size; signed; limit } in
    let result, alarm = search_char kind ~length state str in
    result, alarm || not valid
  with | Abstract_interp.Error_Top
       | Cvalue.V.Not_based_on_null -> return_top ~length str, true

(* Applies the [builtin] built by [do_search]. *)
let apply_builtin _name builtin = fun state args ->
  let args = List.map snd args in
  let result, _alarm = builtin state args in
  let result = if Cvalue.V.is_bottom result then [] else [result] in
  Builtins.Result result

(* Builds, registers and exports a builtin for the C function [c_name]. *)
let register_builtin c_name ~search ~stop_at_0 ~typ ~length ?limit =
  let name = "Frama_C_" ^ c_name in
  let f = do_search ~search ~stop_at_0 ~typ ~length ?limit in
  let builtin = apply_builtin name f in
  Builtins.register_builtin name ~replace:c_name Cacheable builtin;
  f

type str_builtin_sig =
  Cvalue.Model.t -> Cvalue.V.t list -> Cvalue.V.t * bool

let frama_c_strlen_wrapper : str_builtin_sig =
  register_builtin "strlen"
    ~search:Ival.zero ~stop_at_0:false ~typ:Char ~length:true ?limit:None

let _frama_c_strnlen_wrapper =
  register_builtin "strnlen"
    ~search:Ival.zero ~stop_at_0:false ~typ:Char ~length:true ~limit:1

let frama_c_memchr_off_wrapper =
  do_search
    ~search:Ival.bottom ~stop_at_0:false ~typ:Char ~length:true ~limit:2

let _frama_c_memchr_wrapper =
  register_builtin "memchr"
    ~search:Ival.bottom ~stop_at_0:false ~typ:Char ~length:false ~limit:2

let _frama_c_rawmemchr_wrapper =
  register_builtin "rawmemchr"
    ~search:Ival.bottom ~stop_at_0:false ~typ:Char ~length:false ?limit:None

let frama_c_strchr_wrapper =
  register_builtin "strchr"
    ~search:Ival.bottom ~stop_at_0:true ~typ:Char ~length:false ?limit:None

let frama_c_wcslen_wrapper =
  register_builtin "wcslen"
    ~search:Ival.zero ~stop_at_0:false ~typ:Wide ~length:true ?limit:None

let frama_c_wmemchr_off_wrapper =
  do_search
    ~search:Ival.bottom ~stop_at_0:false ~typ:Wide ~length:true ~limit:2

let frama_c_wcschr_wrapper =
  register_builtin "wcschr"
    ~search:Ival.bottom ~stop_at_0:true ~typ:Wide ~length:false ?limit:None

let _frama_c_wmemchr_wrapper =
  register_builtin "wmemchr"
    ~search:Ival.bottom ~stop_at_0:false ~typ:Wide ~length:false ~limit:2
