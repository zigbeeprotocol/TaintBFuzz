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
(* --- VList Builtins                                                     --- *)
(* -------------------------------------------------------------------------- *)
let dkey = Wp_parameters.register_category "sequence"
let debug fmt = Wp_parameters.debug ~dkey fmt
let debugN level fmt = Wp_parameters.debug ~level ~dkey fmt

open Lang
open Lang.F
module L = Qed.Logic
module E = Qed.Engine

(* -------------------------------------------------------------------------- *)
(* --- Driver                                                             --- *)
(* -------------------------------------------------------------------------- *)

let library = "vlist"

(*--- Linked Symbols ---*)

let t_list = "\\list"
let l_list = "list"
let l_concat = E.F_right "concat"
let l_elt = E.(F_call "elt")
let l_repeat = E.(F_call "repeat")

(*--- Typechecking ---*)

let () = LogicBuiltins.add_type t_list ~library ~link:l_list ()
let a_list = Lang.get_builtin_type ~name:t_list

let vlist_get_tau = function
  | None -> invalid_arg "a list operator without result type"
  | Some t -> t

let ty_nil = function _ -> invalid_arg "All nil must be typed"

let ty_listelt = function
  | L.Data(_,[t]) -> (t : tau)
  | _ -> raise Not_found

let ty_cons = function
  | [ _ ; Some l ] -> l
  | [ Some e ; _ ] -> L.Data(a_list,[e])
  | _ -> raise Not_found

let ty_elt = function
  | [ Some e ] -> L.Data(a_list,[e])
  | _ -> raise Not_found

let ty_nth = function
  | Some l :: _ -> ty_listelt l
  | _ -> raise Not_found

let rec ty_concat = function
  | Some l :: _ -> l
  | None :: w -> ty_concat w
  | [] -> raise Not_found

let ty_repeat = function
  | Some l :: _ -> l
  | _ -> raise Not_found

(*--- Qed Symbols ---*)

let f_cons = Lang.extern_f ~library ~typecheck:ty_cons "cons" (* rewriten in concat(elt) *)
let f_nil  = Lang.extern_f ~library ~typecheck:ty_nil ~category:L.Constructor "nil"
let f_elt = Lang.extern_f ~library ~category:L.Constructor ~typecheck:ty_elt ~link:l_elt "elt"

let concatenation = L.(Operator {
    invertible = true ;
    associative = true ;
    commutative = false ;
    idempotent = false ;
    neutral = E_fun(f_nil,[]) ;
    absorbant = E_none ;
  })

let f_nth    = Lang.extern_f ~library ~typecheck:ty_nth "nth"
let f_length = Lang.extern_f ~library ~sort:L.Sint "length"
let f_concat = Lang.extern_f ~library ~category:concatenation ~typecheck:ty_concat ~link:l_concat "concat"
let f_repeat = Lang.extern_f ~library ~typecheck:ty_repeat ~link:l_repeat "repeat"

(*--- ACSL Builtins ---*)

let () =
  let open LogicBuiltins in
  begin
    add_builtin "\\Nil" [] f_nil ;
    add_builtin "\\Cons" [A;A] f_cons ;
    add_builtin "\\nth" [A;Z] f_nth ;
    add_builtin "\\length" [A] f_length ;
    add_builtin "\\concat" [A;A] f_concat ;
    add_builtin "\\repeat" [A;Z] f_repeat ;
  end

let category e =
  match F.repr e with
  | Qed.Logic.Fun (f,_) when Fun.equal f f_nil -> "Nil"
  | Qed.Logic.Fun (f,_) when Fun.equal f f_cons -> "Cons"
  | Qed.Logic.Fun (f,_) when Fun.equal f f_nth -> "Nth"
  | Qed.Logic.Fun (f,_) when Fun.equal f f_length -> "Length"
  | Qed.Logic.Fun (f,_) when Fun.equal f f_concat -> "Concat"
  | Qed.Logic.Fun (f,_) when Fun.equal f f_repeat -> "Repeat"
  | _ -> "_"

let rec pp_pattern fmt e =
  match F.repr e with
  | Qed.Logic.Fun (f, args) when Fun.equal f f_nil ||
                                 Fun.equal f f_cons ||
                                 Fun.equal f f_nth ||
                                 Fun.equal f f_length ||
                                 Fun.equal f f_concat ||
                                 Fun.equal f f_repeat -> Format.fprintf fmt "(%s %a)" (category e) (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ") pp_pattern) args
  | _ -> Format.pp_print_string fmt "_"

(*--- Smart Constructors ---*)

let is_nil e = (* under-approximation of e==[] *)
  match F.repr e with
  | Qed.Logic.Fun (f,_) -> Fun.equal f f_nil
  | _ -> false

let v_nil t = F.e_fun ~result:t f_nil []
let v_elt e = F.e_fun f_elt [e]
let v_concat es tau = F.e_fun f_concat es ~result:tau
let v_length l = F.e_fun f_length [l]
let v_repeat s n tau = F.e_fun f_repeat [s;n] ~result:tau

(* -------------------------------------------------------------------------- *)
(* --- Rewriters                                                          --- *)
(* -------------------------------------------------------------------------- *)

let rewrite_cons a w tau = (* a::w == [a]^w *)
  v_concat [v_elt a ; w] (vlist_get_tau tau)

let rewrite_length e =
  match F.repr e with
  | L.Fun( nil , [] ) when nil == f_nil -> F.e_zero (* \length([]) == 0 *)
  | L.Fun( elt , [_] ) when elt == f_elt -> F.e_one (* \length([x]) == 1 *)
  | L.Fun( concat , es ) when concat == f_concat -> (* \length(\concat(...,x_i,...)) == \sum(...,\length(x_i),...)  *)
    F.e_sum (List.map v_length es)
  | L.Fun( repeat , [ u ; n ] ) when repeat == f_repeat ->
    (* \length(u ^* n) == if 0<=n then n * \length(u) else 0 *)
    F.e_if (F.e_leq e_zero n) (F.e_mul n (v_length u)) e_zero
  | _ ->
    (* NB. do not considers \Cons because they are removed *)
    raise Not_found

let match_natural k =
  match F.repr k with
  | L.Kint z ->
    let k = try Integer.to_int_exn z with Z.Overflow -> raise Not_found in
    if 0 <= k then k else raise Not_found
  | _ -> raise Not_found

(* Why3 definition: [\nth(e,k)] is undefined for [k<0 || k>=\length(e)].
   So, the list cannot be destructured when the length is unknown  *)
let rec get_nth k e =
  match F.repr e with
  | L.Fun( concat , list ) when concat == f_concat -> get_nth_list k list
  | L.Fun( elt , [x] ) when elt == f_elt ->
    get_nth_elt k x (fun _ -> raise Not_found)
  | L.Fun( repeat , [x;n] ) when repeat == f_repeat ->
    get_nth_repeat k x n (fun _ -> raise Not_found)
  | _ -> raise Not_found

and get_nth_list k = function
  | head::tail ->
    begin
      match F.repr head with
      | L.Fun( elt , [x] ) when elt == f_elt ->
        get_nth_elt k x (fun k -> get_nth_list k tail)
      | L.Fun( repeat , [x;n] ) when repeat == f_repeat ->
        get_nth_repeat k x n (fun k -> get_nth_list k tail)
      | _ -> raise Not_found
    end
  | [] -> raise Not_found

and get_nth_elt k x f =
  if k = 0 then x else (f (k-1))

and get_nth_repeat k x n f =
  let n = match_natural n in
  if n = 0 then raise Not_found ;
  let m = match_natural (rewrite_length x) in
  if m = 0 then raise Not_found ;
  let en = Integer.of_int n in
  let em = Integer.of_int m in
  let ek = Integer.of_int k in
  if Integer.(ge ek (mul en em)) then f (k -(n*m))
  else get_nth (k mod m) x

let rewrite_nth s k =
  get_nth (match_natural k) s

let rewrite_repeat s n =
  if F.decide (F.e_leq n e_zero) then (* n <=0 ==> (s *^ n) == [] *)
    v_nil (F.typeof s)
  else if F.equal n e_one then (* (s *^ 1) == s *)
    s
  else if is_nil s then (* ([] *^ n) == [] ; even if [n] is negative *)
    s
  else
    match F.repr s with
    | L.Fun( repeat , [s0 ; n0] ) (* n0>=0 && n>=0 ==> ((s0 *^ n0) *^ n) == (s0 *^ (n0 * n)) *)
      when (repeat == f_repeat) &&
           (Cint.is_positive_or_null n) &&
           (Cint.is_positive_or_null n0) -> v_repeat s0 (F.e_mul n0 n) (F.typeof s)
    | _ -> raise Not_found

let rec leftmost a ms =
  match F.repr a with
  | L.Fun( concat , e :: es ) when concat == f_concat ->
    leftmost e (es@ms)
  | L.Fun( repeat , [ u ; n ] ) when repeat == f_repeat -> begin
      match (* tries to perform some rolling that do not depend on [n] *)
        (match ms with
         | b::ms ->
           let b,ms = leftmost b ms in
           let u,us = leftmost u [] in
           if F.decide (F.e_eq u b) then
             (*  u=b ==>  ((u^us)*^n) ^ b ^ ms  == u ^ (us^b)*^n) ^ ms *)
             Some (u, v_repeat (v_concat (us@[b]) (F.typeof a)) n (F.typeof a) :: ms)
           else None
         | _ -> None) with
      | Some res -> res
      | None ->
        if F.decide (F.e_lt F.e_zero n) then
          (* 0<n ==> (u*^n) ^ ms ==  u ^ (u*^(n-1)) ^ ms *)
          leftmost u (v_repeat u (F.e_sub n F.e_one) (F.typeof a) :: ms)
        else a , ms
    end
  | _ -> a , ms

(* [leftmost a] returns [s,xs] such that [a = s ^ x1 ^ ... ^ xn] *)
let leftmost a =
  let r = leftmost a [] in
  debugN 2 "Vlist.leftmost %a@ = %a (form: %s) ^ ... (%d more)@."
    Lang.F.pp_term a
    Lang.F.pp_term (fst r) (category (fst r))
    (List.length (snd r)) ;
  r

let rec rightmost ms a =
  match F.repr a with
  | L.Fun( concat , es ) when concat == f_concat ->
    begin match List.rev es with
      | [] -> ms , a
      | e::es -> rightmost (ms @ List.rev es) e
    end
  | L.Fun( repeat , [ u ; n ] ) when repeat == f_repeat -> begin
      match (* tries to perform some rolling that do not depend on [n] *)
        (match List.rev ms with
         | b::ms ->
           let ms,b = rightmost (List.rev ms) b in
           let us,u = rightmost [] u in
           if F.decide (F.e_eq u b) then
             (*  u=b ==>  (ms ^ b ^ (us^u)*^n) == ms ^ (b^us)*^n) ^ u *)
             Some (ms @ [ v_repeat (v_concat (b::us) (F.typeof a)) n (F.typeof a)], u)
           else None
         | _ -> None) with
      | Some res -> res
      | None ->
        if F.decide (F.e_lt F.e_zero n) then
          (* 0<n ==> ms ^ (u*^n) ==  ms ^ (u*^(n-1)) ^ u *)
          rightmost (ms @ [v_repeat u (F.e_sub n F.e_one) (F.typeof a)]) u
        else ms , a
    end
  | _ -> ms , a

(* [rightmost a] returns [s,xs] such that [a = x1 ^ ... ^ xn ^ s] *)
let rightmost a =
  let r = rightmost [] a in
  debugN 2 "Vlist.rightmost %a@ = (%d more) ... ^ %a (form: %s)@."
    Lang.F.pp_term a
    (List.length (fst r))
    Lang.F.pp_term (snd r) (category (snd r));
  r

let leftmost_eq a b =
  let a , u = leftmost a in
  let b , v = leftmost b in
  if u <> [] || v <> [] then
    match F.is_equal a b with
    | L.Yes ->
      (* s ^ u1 ^ ...  = s ^ v1 ^ ...  <=>  u1 ^ ... = v1 ^ ... *)
      F.p_equal (v_concat u (F.typeof a)) (v_concat v (F.typeof a))
    | L.No when F.decide (F.e_eq (v_length a) (v_length b)) ->
      (* a <> b && \length(a)=\length(b) ==> a ^ u1 ^ ... <> b ^ v1 ^ ... *)
      F.p_false
    | _ -> raise Not_found
  else
    raise Not_found

let rightmost_eq a b =
  let u , a = rightmost a in
  let v , b = rightmost b in
  if u <> [] || v <> [] then
    match F.is_equal a b with
    | L.Yes ->
      (* u1 ^ ... ^ s = v1 ^ ... ^ s  <=>  u1 ^ ... = v1 ^ ... *)
      F.p_equal (v_concat u (F.typeof a)) (v_concat v (F.typeof a))
    | L.No when F.decide (F.e_eq (v_length a) (v_length b)) ->
      (* a <> b && \length(a)=\length(b) ==> u1 ^ ... ^ a <> v1 ^ ... ^ b *)
      F.p_false
    | _ -> raise Not_found
  else
    raise Not_found

let rewrite_is_nil ~nil a =
  let p_is_nil a = F.p_equal nil a  in
  match F.repr a with
  | L.Fun(concat,es) when concat == f_concat ->
    (* \concat (s1,...,sn)==[] <==> (s1==[] && ... && sn==[]) *)
    F.p_all p_is_nil es
  | L.Fun(elt,[_]) when elt == f_elt -> F.p_false (* [x]==[] <==> false *)
  | L.Fun(repeat,[s;n]) when repeat == f_repeat ->
    (* (s *^ n)==[] <==> (s==[] || n<=0)  *)
    F.p_or (F.p_leq n F.e_zero) (p_is_nil s)
  | _ ->
    raise Not_found

(* Ensures xs to be a sub-sequence of ys, otherwise raise Not_found
   In such a case, (concat xs = concat ys) <==> (forall r in result, r = nil) *)
let rec subsequence xs ys =
  match xs , ys with
  | [],ys -> ys
  | x::rxs, y::rys ->
    if (F.decide (e_eq x y)) then subsequence rxs rys else y :: subsequence xs rys
  | _ -> raise Not_found

let elements a =
  match F.repr a with
  | L.Fun(concat,es) when concat == f_concat -> true, es
  | _ -> false, [ a ]

(* Ensures that [a] or [b] is a sub-sequence of the other, otherwise [raise Not_found]
   In such a case, (concat xs = concat ys) <==> (forall r in result, r = nil) *)
let subsequence a b =
  let destruct_a, xs = elements a in
  let destruct_b, ys = elements b in
  if not (destruct_a || destruct_b) then raise Not_found;
  let shortest,xs,ys = if List.length xs <= List.length ys then a,xs,ys else b,ys,xs in
  let es = subsequence xs ys in
  (* xs=ys <==> forall s in es ; s = nil *)
  let nil = v_nil (F.typeof shortest) in
  (* [s] are elements of [ys] (the longest sequence) and [nil] has the same type than the [shortest] sequence *)
  let p_is_nil s = F.p_equal nil s in
  F.p_all p_is_nil es

let repeat_eq a x n b y m =
  let e_eq_x_y = F.e_eq x y in
  let e_eq_n_m = F.e_eq n m in
  if F.decide e_eq_x_y then
    (* s *^ n == s *^ m  <==>  ( n=m || (s *^ n == [] && s *^ m == []) ) *)
    let nil_a = v_nil (F.typeof a) in
    let nil_b = v_nil (F.typeof b) in
    F.p_or (Lang.F.p_bool e_eq_n_m)
      (F.p_and (F.p_equal a nil_b) (F.p_equal nil_a b))
  else if F.decide e_eq_n_m then
    (* x *^ n == y *^ n  <==> ( x == y || n<=0 ) *)
    F.p_or (F.p_leq n e_zero) (Lang.F.p_bool e_eq_x_y)
  else if F.decide (e_eq (v_length x) (v_length y)) then
    (* \length(x)=\length(y)  ==> ( x *^ n == y *^ m  <==> ( m == n && x == y) || (x *^ n == [] && y *^ m == [] ) *)
    let nil_a = v_nil (F.typeof a) in
    let nil_b = v_nil (F.typeof b) in
    F.p_or (F.p_and (F.p_bool e_eq_n_m) (Lang.F.p_bool e_eq_x_y))
      (F.p_and (F.p_equal a nil_b) (F.p_equal nil_a b))
  else raise Not_found

let rewrite_eq_sequence a b =
  debug "Vlist.rewrite_eq_sequence: tries to rewrite %a@ = %a@.- left pattern:  %a@.- right pattern: %a@."
    Lang.F.pp_term a Lang.F.pp_term b
    pp_pattern a pp_pattern b;
  match F.repr a , F.repr b with
  | L.Fun(nil,[]) , _ when nil == f_nil -> rewrite_is_nil ~nil:a b
  | _ , L.Fun(nil,[]) when nil == f_nil -> rewrite_is_nil ~nil:b a
  | _ -> try
      match F.repr a , F.repr b with
      | L.Fun(repeat_a, [x;n]), L.Fun(repeat_b, [y;m])
        when repeat_a == f_repeat &&
             repeat_b == f_repeat ->
        repeat_eq a x n b y m
      | _ ->
        try leftmost_eq a b with Not_found ->
        try rightmost_eq a b with Not_found ->
          subsequence a b
    with Not_found ->
      if F.decide (F.e_neq (v_length a) (v_length b)) then
        F.p_false
      else raise Not_found

let rewrite_eq_length a b =
  match F.repr a , F.repr b with
  | L.Fun(length_a,[_]), L.Fun(length_b,[_]) when length_a == f_length &&
                                                  length_b == f_length ->
    (* N.B. cannot be simplified by the next patterns *)
    raise Not_found
  | _, L.Fun(length,[_]) when length == f_length &&
                              F.decide (e_lt a e_zero) ->
    (* a < 0  ==>  ( a=\length(b) <=> false ) *)
    F.p_false
  | L.Fun(length,[_]), _ when length == f_length &&
                              F.decide (e_lt b e_zero) ->
    (* b < 0  ==>  ( \length(a)<=b <=> false ) *)
    F.p_false
  | _ -> raise Not_found

let rewrite_leq_length a b =
  match F.repr a , F.repr b with
  | L.Fun(length_a,[_]), L.Fun(length_b,[_]) when length_a == f_length &&
                                                  length_b == f_length ->
    (* N.B. cannot be simplified by the next patterns *)
    raise Not_found
  | L.Fun(length,[_]), _ when length == f_length &&
                              F.decide (e_lt b e_zero) ->
    (* b < 0  ==>  ( \length(a)<=b <=> false ) *)
    F.e_false
  (* N.B. the next rule does not allow to split on the sign of \length(a) with TIP
     | _, L.Fun(length,[_]) when length == f_length &&
                              F.decide (e_leq a e_zero) ->
        (* a <= 0  ==>  ( a<=\length(b) <=> true ) *)
      F.e_true
  *)
  | _ -> raise Not_found


(* All Simplifications *)

let () =
  Context.register
    begin fun () ->
      F.set_builtin_2 f_nth rewrite_nth ;
      F.set_builtin_2' f_cons rewrite_cons ;
      F.set_builtin_2 f_repeat rewrite_repeat ;
      F.set_builtin_1 f_length rewrite_length ;
      F.set_builtin_leq f_length rewrite_leq_length ;
      F.set_builtin_eqp f_length rewrite_eq_length ;
      F.set_builtin_eqp f_concat rewrite_eq_sequence ;
      F.set_builtin_eqp f_repeat rewrite_eq_sequence ;
      F.set_builtin_eqp f_nil rewrite_eq_sequence ;
    end

(* -------------------------------------------------------------------------- *)
(* --- Typing                                                             --- *)
(* -------------------------------------------------------------------------- *)

let f_list = [ f_nil ; f_cons ; f_elt ; f_repeat ; f_concat ]

let check_tau = Lang.is_builtin_type ~name:t_list

let check_term e =
  try match F.repr e with
    | L.Fvar x -> check_tau (F.tau_of_var x)
    | L.Bvar(_,t) -> check_tau t
    | L.Fun( f , _ ) -> List.memq f f_list || check_tau (Lang.F.typeof e)
    | _ -> false
  with Not_found -> false


let f_vlist_eq = Lang.extern_f ~library ~sort:L.Sprop "vlist_eq"

let specialize_eq_list =
  {For_export.for_tau = check_tau;
   mk_new_eq = (fun a b -> Lang.F.e_fun ~result:Qed.Logic.Prop f_vlist_eq [a;b])}

(* -------------------------------------------------------------------------- *)
(* --- Export                                                             --- *)
(* -------------------------------------------------------------------------- *)

class type engine =
  object
    method callstyle : Qed.Engine.callstyle
    method pp_atom : Format.formatter -> Lang.F.term -> unit
    method pp_flow : Format.formatter -> Lang.F.term -> unit
  end

let rec export (engine : #engine) fmt = function
  | [] ->
    begin match engine#callstyle with
      | E.CallVoid -> Format.pp_print_string fmt "nil()"
      | E.CallVar|E.CallApply -> Format.pp_print_string fmt "nil"
    end
  | e::es ->
    begin match F.repr e with
      | L.Fun( elt , [x] ) when elt == f_elt ->
        apply engine fmt "cons" x es
      | _ ->
        apply engine fmt "concat" e es
    end

and apply (engine : #engine) fmt f x es =
  match engine#callstyle with
  | E.CallVar | E.CallVoid ->
    Format.fprintf fmt "@[<hov 2>%s(@,%a,@,%a)@]"
      f engine#pp_flow x (export engine) es
  | E.CallApply ->
    Format.fprintf fmt "@[<hov 2>(%s@ %a@ %a)@]"
      f engine#pp_atom x (export engine) es


let export_rewriter_concat es tau =
  match es with
  | [] -> v_nil (vlist_get_tau tau)
  | e::es ->
    begin match F.repr e with
      | L.Fun( elt , [x] ) when Lang.Fun.equal elt f_elt ->
        e_fun ?result:tau f_cons [x;e_fun ?result:tau f_concat es]
      | _ -> raise Not_found
    end

let () =
  Lang.For_export.set_builtin' f_concat export_rewriter_concat

(* -------------------------------------------------------------------------- *)

let rec collect xs = function
  | [] -> List.rev xs , []
  | (e::es) as w ->
    begin match F.repr e with
      | L.Fun( elt , [x] ) when elt == f_elt -> collect (x::xs) es
      | _ -> List.rev xs , w
    end

let list engine fmt xs = Qed.Plib.pp_listsep ~sep:"," engine#pp_flow fmt xs

let elements (engine : #engine) fmt xs =
  Format.fprintf fmt "@[<hov 2>[ %a ]@]" (list engine) xs

let rec pp_concat (engine : #engine) fmt es =
  let xs , es = collect [] es in
  begin
    (if xs <> [] then elements engine fmt xs) ;
    match es with
    | [] -> ()
    | m::ms ->
      if xs <> [] then Format.fprintf fmt " ^@ " ;
      engine#pp_atom fmt m ;
      if ms <> [] then
        ( Format.fprintf fmt " ^@ " ; pp_concat engine fmt ms )
  end

let pretty (engine : #engine) fmt es =
  if es = [] then Format.pp_print_string fmt "[]" else
    Format.fprintf fmt "@[<hov 2>%a@]" (pp_concat engine) es

let pprepeat (engine : #engine) fmt = function
  | [l;n] -> Format.fprintf fmt "@[<hov 2>(%a *^@ %a)@]" engine#pp_flow l engine#pp_flow n
  | es -> Format.fprintf fmt "@[<hov 2>repeat(%a)@]" (list engine) es

let shareable e =
  match F.repr e with
  | L.Fun( f , es ) -> f != f_elt && es != []
  | _ -> true

(* -------------------------------------------------------------------------- *)
