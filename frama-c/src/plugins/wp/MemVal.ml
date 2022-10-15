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

(* -------------------------------------------------------------------------- *)
(* --- Value Separation Analysis' Based Memory Model                      --- *)
(* -------------------------------------------------------------------------- *)

open Cil_types
open Cil_datatype
open Ctypes
open Lang
open Lang.F
open Sigs
open Definitions

module Logic = Qed.Logic

module type State =
sig
  type t

  val bottom : t
  val join : t -> t -> t

  val of_kinstr : Cil_types.kinstr -> t
  val of_stmt : Cil_types.stmt -> t
  val of_kf : Cil_types.kernel_function -> t

  val pretty : Format.formatter -> t -> unit
end

module type Value =
sig
  val configure : unit -> WpContext.rollback
  val datatype : string

  module State : State

  type t
  type state = State.t

  val null : t
  val literal: eid:int -> Cstring.cst -> int * t
  val cvar : varinfo -> t

  val field : t -> Cil_types.fieldinfo -> t
  val shift : t -> Ctypes.c_object -> term -> t
  val base_addr : t -> t

  val load : state -> t -> Ctypes.c_object -> t

  val domain : t -> Base.t list
  val offset : t -> (term -> pred)

  val pretty : Format.formatter -> t -> unit
end

module type Base =
sig
end

let dkey = Wp_parameters.register_category "memval" (* Debugging key *)
let dkey_val = Wp_parameters.register_category "memval:val"

let debug fmt = Wp_parameters.debug ~dkey fmt
let debug_val = Wp_parameters.debug ~dkey:dkey_val


(* -------------------------------------------------------------------------- *)
(* ---  Logic Memory Wrapper                                              --- *)
(* -------------------------------------------------------------------------- *)
let library = "memory"

let a_addr = Lang.datatype ~library "addr"
let t_addr = Logic.Data(a_addr,[])
let f_base   = Lang.extern_f ~library ~result:Logic.Int
    ~link:(Qed.Engine.F_subst ("base", "%1.base")) "base"
let f_offset = Lang.extern_f ~library ~result:Logic.Int
    ~link:(Qed.Engine.F_subst ("offset", "%1.offset")) "offset"
let f_shift  = Lang.extern_f ~library ~result:t_addr "shift"
let f_global = Lang.extern_f ~library ~result:t_addr "global"
let f_null   = Lang.extern_f ~library ~result:t_addr "null"

let a_null = F.constant (e_fun f_null []) (* { base = 0; offset = 0 } *)
let a_base p = e_fun f_base [p]           (* p -> p.offset *)
let a_offset p = e_fun f_offset [p]       (* p -> p.base *)
let a_global b = e_fun f_global [b]       (* b -> { base = b; offset = 0 } *)
let a_shift l k = e_fun f_shift [l;k]     (* p k -> { p w/ offset = p.offset + k } *)
let a_addr b k = a_shift (a_global b) k   (* b k -> { base = b; offset = k } *)

(* -------------------------------------------------------------------------- *)
(* ---  Cmath Wrapper                                                     --- *)
(* -------------------------------------------------------------------------- *)
let a_iabs i = e_fun ~result:Logic.Int Cmath.f_iabs [i]    (* x -> |x| *)

(* -------------------------------------------------------------------------- *)
(* ---  MemValue Types                                                     --- *)
(* -------------------------------------------------------------------------- *)
(* Model utilities *)
let t_words = Logic.Array (Logic.Int, Logic.Int) (* TODO: A way to abstract this ? *)

(* -------------------------------------------------------------------------- *)
(* ---  Qed Simplifiers                                                   --- *)
(* -------------------------------------------------------------------------- *)
let phi_base t = match F.repr t with
  | Logic.Fun (f, [p; _]) when f == f_shift -> a_base p
  | Logic.Fun (f, [b]) when f == f_global -> b
  | _ -> raise Not_found

let phi_offset t = match F.repr t with
  | Logic.Fun (f, [p; k]) when f == f_shift -> e_add (a_offset p) k
  | Logic.Fun (f, _) when f == f_global -> F.e_zero
  | _ -> raise Not_found

let phi_shift p i =
  if F.is_zero i then p
  else match F.repr p with
    | Logic.Fun (f, [q; j]) when f == f_shift -> F.e_fun f [q; F.e_add i j]
    (* | Logic.Fun (f, [b]) when f == f_global -> a_addr b i *)
    | _ -> raise Not_found

let _phi_read ~obj ~read ~write mem off = match F.repr mem with
  | Logic.Fun (f, [_; o; v]) when f == write && off == o -> v
  (*read_tau (write_tau m o v) o == v*)
  | Logic.Fun (f, [m; o; _]) when f == write ->
    let offset = a_iabs (F.e_sub off o) in
    if F.eval_leq (F.e_int (Ctypes.sizeof_object obj)) offset then
      F.e_fun read [m; off]
    else raise Not_found
  (*read_tau (write_tau m o v) o' == read m o' when |o - o'| <= sizeof(tau)*)
  | _ -> raise Not_found

let () = Context.register
    begin fun () ->
      F.set_builtin_1 f_base phi_base;
      F.set_builtin_1 f_offset phi_offset;
      F.set_builtin_2 f_shift phi_shift;
    end

(* -------------------------------------------------------------------------- *)
(* ---  Utilities                                                         --- *)
(* -------------------------------------------------------------------------- *)
(* Wp utilities *)
module Cstring =
struct
  include Cstring

  let str_cil ~eid cstr =
    let enode = match cstr with
      | C_str str -> Const (CStr str)
      | W_str wstr -> Const (CWStr wstr)
    in {
      eid = eid;
      enode = enode;
      eloc = Location.unknown;
    }
end

(* Value utilities *)
module Base =
struct
  include Base

  let bitsize_from_validity = function
    | Invalid -> Integer.zero
    | Empty -> Integer.zero
    | Known (_, m)
    | Unknown (_, _, m) -> Integer.succ m
    | Variable { max_allocable } -> Integer.succ max_allocable

  let size_from_validity b =
    Integer.(e_div (bitsize_from_validity b) eight)
end


(* -------------------------------------------------------------------------- *)
(* ---  Memory Model                                                      --- *)
(* -------------------------------------------------------------------------- *)
module Make(V : Value) =
struct
  (* -------------------------------------------------------------------------- *)
  (* ---  Model Parameters                                                  --- *)
  (* -------------------------------------------------------------------------- *)
  let datatype = "MemVal." ^ V.datatype
  let configure () =
    let rollback = V.configure () in
    let orig_pointer = Context.push Lang.pointer t_addr in
    let rollback () =
      rollback ();
      Context.pop Lang.pointer orig_pointer;
    in
    rollback

  module StateRef =
  struct
    let model : V.State.t Context.value = Context.create "Memval.model"
    let get () = Context.get model
    let update () =
      try
        (match WpContext.get_scope () with
         | WpContext.Global -> assert false
         | WpContext.Kf kf -> Context.set model (V.State.of_kf kf))
      with | Invalid_argument _ -> Context.set model (V.State.of_kinstr Kglobal)
           | Kernel_function.No_Definition -> assert false
  end
  (* -------------------------------------------------------------------------- *)
  (* ---  Chunk                                                             --- *)
  (* -------------------------------------------------------------------------- *)
  type chunk =
    | M_base of Base.t

  module Chunk =
  struct
    type t = chunk
    let self = "MemVal.Chunk"
    let hash = function
      | M_base b -> 5 * Base.hash b
    let equal c1 c2 = match c1, c2 with
      | M_base b1, M_base b2 -> Base.equal b1 b2
    let compare c1 c2 = match c1, c2 with
      | M_base b1, M_base b2 -> Base.compare b1 b2
    let pretty fmt = function
      | M_base b -> Base.pretty fmt b
    let tau_of_chunk = function
      | M_base _ -> t_words
    let basename_of_base = function
      | Base.Var (vi, _) -> Format.sprintf "MVar_%s" (LogicUsage.basename vi)
      | Base.CLogic_Var (_, _, _) -> assert false (* not supposed to append. *)
      | Base.Null -> "MNull"
      | Base.String (eid, _) -> Format.sprintf "MStr_%d" eid
      | Base.Allocated (vi, _dealloc, _) ->
        Format.sprintf "MAlloc_%s" (LogicUsage.basename vi)
    let basename_of_chunk = function
      | M_base b -> basename_of_base b
    let is_framed = function
      | M_base b ->
        try
          (match WpContext.get_scope () with
           | WpContext.Global -> assert false
           | WpContext.Kf kf -> Base.is_formal_or_local b (Kernel_function.get_definition kf))
        with Invalid_argument _ | Kernel_function.No_Definition ->
          assert false (* by context. *)
  end

  let cluster () = Definitions.cluster ~id:"MemVal"  ()

  module Heap = Qed.Collection.Make(Chunk)
  module Sigma = Sigma.Make(Chunk)(Heap)

  type loc = {
    loc_v : V.t;
    loc_t : term (* of type addr *)
  }

  type sigma = Sigma.t
  type segment = loc rloc

  type state = unit
  let state _ = ()
  let iter _ _ = ()
  let lookup _ _ = Mterm
  let updates _ _ = Bag.empty
  let apply _ _ = ()

  let pretty fmt l =
    Format.fprintf fmt "([@ t:%a,@ v:%a @])"
      F.pp_term l.loc_t
      V.pretty l.loc_v

  let vars _l = Vars.empty
  let occurs _x _l = false

  (* -------------------------------------------------------------------------- *)
  (* ---  Constructors                                                      --- *)
  (* -------------------------------------------------------------------------- *)
  let null = {
    loc_v = V.null;
    loc_t = a_null;
  }

  let literal ~eid cstr =
    let bid, v = V.literal ~eid cstr in
    {
      loc_v = v;
      loc_t = a_global (F.e_int bid)
    }

  let cvar x = {
    loc_v = V.cvar x;
    loc_t = a_addr (F.e_int (Base.id (Base.of_varinfo x))) (F.e_zero);
  }


  (* -------------------------------------------------------------------------- *)
  (* --- Generated Axiomatization                                           --- *)
  (* -------------------------------------------------------------------------- *)

  module Obj =
  struct
    include C_object

    let compare a b =
      if a==b then 0 else
        match a, b with
        | C_pointer _, C_pointer _ -> 0
        | _ -> compare a b
  end

  module Access = WpContext.Generator(Obj)
      (struct
        let name = "MemVal.Access"
        type key = c_object
        type data = lfun * lfun

        let read suffix t_mem t_data  =
          let result = t_data in
          let lfun = Lang.generated_f ~result "read_%s" suffix in
          let xw = Lang.freshvar ~basename:"w" t_mem in
          let xo = Lang.freshvar ~basename:"o" Logic.Int in
          let dfun = Definitions.Logic result in
          let cluster = cluster () in
          Definitions.define_symbol {
            d_lfun = lfun; d_types = 0;
            d_params = [xw; xo];
            d_definition = dfun;
            d_cluster = cluster;
          };
          lfun

        let write suffix t_mem t_data =
          let result = t_mem in
          let lfun = Lang.generated_f ~result "write_%s" suffix in
          let xw = Lang.freshvar ~basename:"w" t_mem in
          let xo = Lang.freshvar ~basename:"o" Logic.Int in
          let xv = Lang.freshvar ~basename:"v" t_data in
          let dfun = Definitions.Logic result in
          let cluster = cluster () in
          Definitions.define_symbol {
            d_lfun = lfun; d_types = 0;
            d_params = [xw; xo; xv];
            d_definition = dfun;
            d_cluster = cluster;
          };
          lfun

        let axiomatize ~obj:_ suffix t_mem t_data f_rd f_wr =
          let name = "axiom_" ^ suffix in
          let xw = Lang.freshvar ~basename:"w" t_mem in
          let w = e_var xw in
          let xo = Lang.freshvar ~basename:"o" Logic.Int in
          let o = e_var xo in
          let xv = Lang.freshvar ~basename:"v" t_data in
          let v = e_var xv in
          let p_write = e_fun f_wr [w; o; v] ~result:t_mem in
          let p_read = e_fun f_rd [p_write; o] ~result:t_data in
          let lemma = p_equal p_read v in
          let cluster = cluster () in
          (* if not (Wp_parameters.debug_atleast 1) then begin
           *   F.set_builtin_2 f_rd (phi_read ~obj ~read:f_rd ~write:f_wr)
           * end; *)
          Definitions.define_lemma {
            l_kind = Cil_types.Admit;
            l_name = name; l_types = 0;
            l_triggers = [];
            l_forall = [xw; xo; xv];
            l_lemma = lemma;
            l_cluster = cluster;
          }

        let axiomatize2 ~obj suffix t_mem t_data f_rd f_wr =
          let name = "axiom_" ^ suffix ^ "_2" in
          let xw = Lang.freshvar ~basename:"w" t_mem in
          let w = e_var xw in
          let xwo = Lang.freshvar ~basename:"xwo" Logic.Int in
          let wo = e_var xwo in
          let xro = Lang.freshvar ~basename:"xro" Logic.Int in
          let ro = e_var xro in
          let xv = Lang.freshvar ~basename:"v" t_data in
          let v = e_var xv in
          let p_write = e_fun f_wr [w; wo; v] ~result:t_mem in
          let p_read = e_fun f_rd [p_write; ro] ~result:t_data in
          let sizeof = (F.e_int (Ctypes.sizeof_object obj)) in
          let offset = a_iabs (F.e_sub ro wo) in
          let lemma =
            F.p_imply
              (F.p_leq sizeof offset)
              (F.p_equal p_read (e_fun f_rd [w; ro] ~result:t_data))
          in
          let cluster = cluster () in
          Definitions.define_lemma {
            l_kind = Cil_types.Admit;
            l_name = name; l_types = 0;
            l_triggers = [];
            l_forall = [xw; xwo; xro; xv];
            l_lemma = lemma;
            l_cluster = cluster;
          }

        let generate obj =
          let suffix = Ctypes.basename obj in
          let t_mem = t_words in
          let t_data = Lang.tau_of_object obj in
          let d_read = read suffix t_mem t_data in
          let d_write = write suffix t_mem t_data in
          axiomatize ~obj suffix t_mem t_data d_read d_write;
          axiomatize2 ~obj suffix t_mem t_data d_read d_write;
          d_read, d_write

        let compile = Lang.local generate
      end)

  let read obj ~mem ~offset =
    F.e_fun (fst (Access.get obj)) [mem; offset] ~result:(Lang.tau_of_object obj)
  let write obj ~mem ~offset ~value =
    F.e_fun (snd (Access.get obj)) [mem; offset; value] ~result:t_words

  let fold_ite f l =
    let rec aux = function
      | [] -> assert false
      | [x] -> f x
      | x :: xs ->
        F.e_if
          (F.e_eq (a_base l.loc_t) (F.e_int (Base.id x)))
          (f x)
          (aux xs)
    in
    aux (V.domain l.loc_v)

  let fold_ite_pred f l =
    let rec aux = function
      | [] -> assert false
      | [x] -> f x
      | x :: xs ->
        F.p_if
          (F.p_equal (a_base l.loc_t) (F.e_int (Base.id x)))
          (f x)
          (aux xs)
    in
    aux (V.domain l.loc_v)

  (* -------------------------------------------------------------------------- *)
  (* ---  Logic to Location (and resp.)                                     --- *)
  (* -------------------------------------------------------------------------- *)
  let pointer_loc _ = Warning.error ~source:"MemVal" "Cannot build top from EVA"

  let pointer_val l = l.loc_t


  (* -------------------------------------------------------------------------- *)
  (* ---  Lifting                                                           --- *)
  (* -------------------------------------------------------------------------- *)
  let field l fd =
    let offs = Integer.of_int (Ctypes.field_offset fd) in
    {
      loc_v = V.field l.loc_v fd;
      loc_t = a_shift l.loc_t (F.e_bigint offs);
    }

  let shift l obj k =
    let size = Integer.of_int (Ctypes.sizeof_object obj) in
    let offs = F.e_times size k in
    {
      loc_v = V.shift l.loc_v obj k;
      loc_t = a_shift l.loc_t offs;
    }

  let base_addr l =
    {
      loc_v = V.base_addr l.loc_v;
      loc_t = a_addr (a_base l.loc_t) F.e_zero;
    }

  let block_length _s _obj l =
    let size_from_base base =
      F.e_bigint Base.(size_from_validity (validity base))
    in
    fold_ite size_from_base l

  (* -------------------------------------------------------------------------- *)
  (* ---  Casting                                                           --- *)
  (* -------------------------------------------------------------------------- *)
  let cast _ l = l

  let loc_of_int _ v =
    if F.is_zero v then null
    else
      (*TODO: Reinterpret integer with Value *)
      Warning.error ~source:"MemVal Model"
        "Forbidden cast of int to pointer"

  let int_of_loc _ l = pointer_val l

  let domain _ l =
    let d = V.domain l.loc_v in
    assert (d <> []);
    List.fold_left
      (fun acc b -> Heap.Set.add (M_base b) acc)
      Heap.Set.empty d

  (* -------------------------------------------------------------------------- *)
  (* ---  Memory Load                                                       --- *)
  (* -------------------------------------------------------------------------- *)
  let load_value sigma obj l =
    let load_base base =
      let mem = Sigma.value sigma (M_base base) in
      let offset = a_offset l.loc_t in
      read obj ~mem ~offset
    in
    let t = fold_ite load_base l in
    begin if Wp_parameters.has_dkey dkey_val then
        let v = V.load (StateRef.get ()) l.loc_v obj in
        debug_val "load: %a -> %a" V.pretty l.loc_v V.pretty v
    end;
    Val t

  let load_loc ~assume sigma obj l =
    let load_base v' base =
      let mem = Sigma.value sigma (M_base base) in
      let offset = a_offset l.loc_t in
      let rd = read obj ~mem ~offset in
      if assume then begin
        let pred = V.offset v' (a_offset rd) in
        Lang.assume pred (* Yet another mutable. *)
      end;
      rd
    in
    let v' = V.load (StateRef.get ()) l.loc_v obj in
    let t = fold_ite (load_base v') l in
    Loc {
      loc_v = V.load (StateRef.get ()) l.loc_v obj;
      loc_t = t;
    }

  let load : sigma -> c_object -> loc -> loc value = fun sigma obj l ->
    StateRef.update ();
    begin match obj with
      | C_int _ | C_float _ -> load_value sigma obj l
      | C_pointer _ -> load_loc ~assume:true sigma obj l
      | _ -> load_loc ~assume:false sigma obj l
    end

  let load_init _sigma obj _loc =
    e_var @@ Lang.freshvar ~basename:"i" @@ Lang.init_of_object obj

  (* -------------------------------------------------------------------------- *)
  (* ---  Memory Store                                                      --- *)
  (* -------------------------------------------------------------------------- *)
  let stored : sigma sequence -> c_object -> loc -> term -> equation list = fun seq obj l v ->
    let mk_write cond base =
      let wpre = Sigma.value seq.pre (M_base base) in
      let wpost = Sigma.value seq.post (M_base base) in
      let write = write obj ~mem:wpre ~offset:(a_offset l.loc_t) ~value:v in
      F.p_equal wpost (F.e_if cond write wpre)
    in
    let rec store acc = function
      | [] -> assert false
      | [c] ->
        let cond = F.e_and ((List.map (F.e_neq (a_base l.loc_t))) acc) in
        [ Assert (mk_write cond c) ]
      | c :: cs ->
        let bid = (F.e_int (Base.id c)) in
        let cond = F.e_eq (a_base l.loc_t) bid in
        [ Assert (mk_write cond c) ]
        @ store (bid :: acc) cs
    in
    store [ ] (V.domain l.loc_v)

  let stored_init _seq _obj _loc _t = []

  let copied seq obj ll lr =
    let v = match load seq.pre obj lr with
      | Sigs.Val v -> v
      | Sigs.Loc l -> l.loc_t
    in
    stored seq obj ll v

  let copied_init _seq _obj _ll _lr = []

  let assigned _s _obj _sloc = [ Assert F.p_true ]


  (* -------------------------------------------------------------------------- *)
  (* ---  Pointer Comparison                                                --- *)
  (* -------------------------------------------------------------------------- *)
  let is_null l = p_equal l.loc_t a_null

  let loc_delta l1 l2 =
    match F.is_equal (a_base l1.loc_t) (a_base l2.loc_t) with
    | Logic.Yes -> F.e_sub (a_offset l1.loc_t) (a_offset l2.loc_t)
    | Logic.Maybe | Logic.No ->
      Warning.error "Can only compare pointers with same base."

  let base_eq l1 l2 = F.p_equal (a_base l1.loc_t) (a_base l2.loc_t)
  let offset_cmp cmpop l1 l2 = cmpop (a_offset l1.loc_t) (a_offset l2.loc_t)

  let loc_diff _obj l1 l2 = loc_delta l1 l2
  let loc_eq l1 l2 = F.p_and (base_eq l1 l2) (offset_cmp F.p_equal l1 l2)
  let loc_lt l1 l2 = F.p_lt (loc_delta l1 l2) F.e_zero
  let loc_leq l1 l2 = F.p_leq (loc_delta l1 l2) F.e_zero
  let loc_neq l1 l2 = F.p_neq (loc_delta l1 l2) F.e_zero

  (* -------------------------------------------------------------------------- *)
  (* --- Segments                                                           --- *)
  (* -------------------------------------------------------------------------- *)

  type range =
    | LOC of loc * term (*size*)
    | RANGE of loc * Vset.set (* offset range access from *loc* *)

  let range_of_rloc = function
    | Rloc (obj, l) ->
      LOC (l, F.e_int (Ctypes.sizeof_object obj))
    | Rrange (l, obj, Some a, Some b) ->
      let la = shift l obj a in
      let n = e_fact (Ctypes.sizeof_object obj) (F.e_range a b) in
      LOC (la, n)
    | Rrange (l, obj, a_opt, b_opt) ->
      let f = F.e_fact (Ctypes.sizeof_object obj) in
      RANGE (l, Vset.range (Option.map f a_opt) (Option.map f b_opt))

  (* -------------------------------------------------------------------------- *)
  (* ---  Validity                                                          --- *)
  (* -------------------------------------------------------------------------- *)
  (** [vset_from_validity base] returns the logical set of all valid bytes of
      [base]. **)
  let vset_from_validity = function
    | Base.Empty -> Vset.empty
    | Base.Invalid -> Vset.singleton F.e_zero
    | Base.Known (min_valid, max_valid)
    | Base.Unknown (min_valid, Some max_valid, _) ->
      (* valid between min_valid .. max_valid inclusive *)
      let mn = F.e_bigint Integer.(e_div min_valid eight) in
      let mx = F.e_bigint Integer.(e_div max_valid eight) in
      Vset.range (Some mn) (Some mx)
    | Base.Variable { Base.min_alloc = min_valid } ->
      (* valid between 0 .. min_valid inclusive *)
      let mn_valid = F.e_bigint Integer.(e_div min_valid eight) in
      Vset.range (Some F.e_zero) (Some mn_valid)
    | Base.Unknown (_, None, _) -> Vset.empty

  let valid_range : sigma -> acs -> range -> pred = fun _ acs r ->
    let for_writing = match acs with RW -> true | RD -> false
                                   | OBJ -> true (* TODO:  *) in
    let l, base_offset = match r with
      | LOC (l, n) ->
        let a = a_offset l.loc_t in
        let b = F.e_add a (F.e_sub n F.e_one) in
        l, Vset.range (Some a) (Some b)
      | RANGE (l, r) -> l, Vset.lift_add (Vset.singleton l.loc_t) r
    in
    let valid_base set base =
      if for_writing && (Base.is_read_only base) then
        F.p_false
      else
        let base_vset = vset_from_validity (Base.validity base) in
        Vset.subset set base_vset
    in
    fold_ite_pred (valid_base base_offset) l

  (** [valid sigma acs seg] returns the formula that tests if a given memory
      segment [seg] (in bytes) is valid (according to [acs]) at memory state
      [sigma]. **)
  let valid : sigma -> acs -> segment -> pred = fun s acs seg ->
    valid_range s acs (range_of_rloc seg)

  let invalid = fun _ _ -> F.p_true (* TODO *)

  (* -------------------------------------------------------------------------- *)
  (* ---  Scope                                                             --- *)
  (* -------------------------------------------------------------------------- *)
  let alloc_sigma : sigma -> varinfo list -> sigma = fun sigma xs ->
    let alloc sigma x =
      let havoc s c = Sigma.havoc_chunk s (M_base c) in
      let v = V.cvar x in
      List.fold_left havoc sigma (V.domain v)
    in
    List.fold_left alloc sigma xs

  let alloc_pred _ _ _ = []

  let alloc sigma xs =
    if xs = [] then sigma else alloc_sigma sigma xs

  let scope : sigma sequence -> scope -> varinfo list -> pred list = fun seq scope xs ->
    match scope with
    | Enter -> []
    | Leave ->
      alloc_pred seq xs ()

  let scope seq sc xs =
    let preds = scope seq sc xs in
    debug "[scope pre:%a post:%a xs:%a] -> preds:%a"
      Sigma.pretty seq.pre
      Sigma.pretty seq.post
      (Pretty_utils.pp_iter ~sep:" " List.iter Varinfo.pretty) xs
      (Pretty_utils.pp_iter ~sep:" " List.iter pp_pred) preds;
    preds

  let global : sigma -> term (*addr*) -> pred = fun _ _ ->
    F.p_true (* True is harmless and WP never call this function... *)


  (* -------------------------------------------------------------------------- *)
  (* ---  Separation                                                        --- *)
  (* -------------------------------------------------------------------------- *)
  let range_to_base_offset = function
    | LOC (l, n) ->
      let a = a_offset l.loc_t in
      let b = F.e_add a n in
      l, Vset.range (Some a) (Some b)
    | RANGE (l, r) -> l, Vset.lift_add (Vset.singleton l.loc_t) r

  let included : segment -> segment -> pred = fun s1 s2 ->
    (* (b1 = b2) -> (r1 \in r2) *)
    let l1, vs1 = range_to_base_offset (range_of_rloc s1) in
    let l2, vs2 = range_to_base_offset (range_of_rloc s2) in
    p_and
      (p_equal (a_base l1.loc_t) (a_base l2.loc_t))
      (Vset.subset vs1 vs2)

  let separated : segment -> segment -> pred = fun s1 s2 ->
    (* (b1 = b2) -> (r1 \cap r2) = \empty *)
    let l1, vs1 = range_to_base_offset (range_of_rloc s1) in
    let l2, vs2 = range_to_base_offset (range_of_rloc s2) in
    p_and
      (p_equal (a_base l1.loc_t) (a_base l2.loc_t))
      (Vset.disjoint vs1 vs2)

  let initialized _sigma _l = F.p_true (* todo *)
  let is_well_formed _ = F.p_true (* todo *)
  let base_offset _loc = assert false (* TODO *)
  type domain = Sigma.domain
  let no_binder = { bind = fun _ f v -> f v }
  let configure_ia _ = no_binder (* todo *)
  let hypotheses x = x (* todo *)
  let frame _sigma = [] (* todo *)

end




(* -------------------------------------------------------------------------- *)
(* ---  EVA Instance                                                      --- *)
(* -------------------------------------------------------------------------- *)
module Eva =
struct
  open Cvalue

  let datatype = "Eva"
  let configure () =
    if not (Db.Value.is_computed ()) then
      Wp_parameters.abort ~current:true
        "Could not use Eva memory model without a previous run of the analysis.";
    (fun () -> ())

  module State =
  struct
    type t = Model.t

    let bottom = Model.bottom
    let join = Model.join

    let of_kinstr k = Db.Value.get_state k
    let of_stmt k = Db.Value.get_stmt_state k
    let of_kf kf =
      let state = ref bottom in
      let vis = object
        inherit Cil.nopCilVisitor
        method !vstmt stmt =
          state := join (of_stmt stmt) !state;
          Cil.DoChildren
      end in
      ignore (Cil.visitCilFunction vis (Kernel_function.get_definition kf));
      !state

    let pretty = Model.pretty
  end

  type t = V.t
  type state = Model.t

  let null = V.inject Base.null Ival.zero
  let literal ~eid cstr =
    let b = Base.of_string_exp (Cstring.str_cil ~eid cstr) in
    Base.id b, V.inject b Ival.zero
  let cvar x = V.inject (Base.of_varinfo x) Ival.zero

  let field v fd =
    let bsize = Ctypes.field_offset fd |> Integer.of_int in
    let offs = Ival.inject_singleton bsize in
    Cvalue.V.shift offs v
  let shift v obj t =
    let bsize = 8 * Ctypes.sizeof_object obj |> Integer.of_int in
    let offs = match F.repr t with
      | Logic.Kint z -> Ival.inject_singleton (Integer.mul bsize z)
      | _ -> Ival.top in
    Cvalue.V.shift offs v
  let base_addr v =
    Cvalue.V.fold_topset_ok
      (fun b _ v -> Cvalue.V.add b Ival.zero v)
      v (Cvalue.V.bottom)

  let load state v obj =
    let bsize = 8 * Ctypes.sizeof_object obj in
    let bits = Locations.loc_bytes_to_loc_bits v in
    let int_base = bsize |> Integer.of_int |> Int_Base.inject in
    let vloc = Locations.make_loc bits int_base in
    Cvalue.Model.find state vloc

  let domain v =
    Cvalue.V.fold_topset_ok
      (fun b _ acc -> b :: acc)
      v []

  let logic_ival ival = fun x ->
    (* assert (not (Ival.is_float ival)); (* by integer offsets *) *)
    match Ival.project_small_set ival with
    | Some is ->
      F.p_any
        (fun i -> F.p_equal x (F.e_bigint i))
        is
    | None -> begin
        match Ival.min_and_max ival with
        | Some mn, Some mx ->
          F.p_and
            (F.p_leq (F.e_bigint mn) x)
            (F.p_leq x (F.e_bigint mx))
        | Some mn, None -> F.p_leq (F.e_bigint mn) x
        | None, Some mx -> F.p_leq x (F.e_bigint mx)
        | None, None -> F.p_true
      end

  let offset v = fun x ->
    let ivals =
      Cvalue.V.fold_topset_ok
        (fun _ ival acc -> ival :: acc)
        v []
    in
    F.p_any (fun ival -> logic_ival ival x) ivals

  let pretty = Cvalue.V.pretty

end
