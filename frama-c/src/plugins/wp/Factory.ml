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
(* --- Model Factory                                                      --- *)
(* -------------------------------------------------------------------------- *)

type mheap = Hoare | ZeroAlias | Region | Typed of MemTyped.pointer | Eva
type mvar = Raw | Var | Ref | Caveat

type setup = {
  mvar : mvar ;
  mheap : mheap ;
  cint : Cint.model ;
  cfloat : Cfloat.model ;
}

(*[LC] All types in [model] must be Stdlib-comparable *)

type driver = LogicBuiltins.driver

(* -------------------------------------------------------------------------- *)
(* --- Description & Id                                                   --- *)
(* -------------------------------------------------------------------------- *)

let main (i,t) name =
  begin
    Buffer.add_string i name ;
    Buffer.add_string t (String.capitalize_ascii name) ;
  end

let add (i,t) part =
  begin
    Buffer.add_char i '_' ;
    Buffer.add_string i part ;
    Buffer.add_char t ' ' ;
    Buffer.add_char t '(' ;
    Buffer.add_string t (String.capitalize_ascii part) ;
    Buffer.add_char t ')' ;
  end

let descr_mtyped d = function
  | MemTyped.NoCast -> add d "nocast"
  | MemTyped.Unsafe -> add d "cast"
  | MemTyped.Fits -> ()

let descr_mheap d = function
  | Region -> main d "region"
  | ZeroAlias -> main d "zeroalias"
  | Hoare -> main d "hoare"
  | Typed p -> main d "typed" ; descr_mtyped d p
  | Eva -> main d "eva"

let descr_mvar d = function
  | Var -> ()
  | Ref -> add d "ref"
  | Raw -> add d "raw"
  | Caveat -> add d "caveat"

let descr_cint d = function
  | Cint.Machine -> ()
  | Cint.Natural -> add d "nat"

let descr_cfloat d = function
  | Cfloat.Real -> add d "real"
  | Cfloat.Float -> ()

let descr_setup (s:setup) =
  begin
    let i = Buffer.create 40 in
    let t = Buffer.create 40 in
    let d = (i,t) in
    descr_mheap d s.mheap ;
    descr_mvar d s.mvar ;
    descr_cint d s.cint ;
    descr_cfloat d s.cfloat ;
    ( Buffer.contents i , Buffer.contents t )
  end

let descriptions = Hashtbl.create 31 (*[LC] Not projectified: simple strings *)
let describe s =
  try Hashtbl.find descriptions s
  with Not_found -> let w = descr_setup s in Hashtbl.add descriptions s w ; w

(* -------------------------------------------------------------------------- *)
(* --- Variable Proxy                                                     --- *)
(* -------------------------------------------------------------------------- *)

let validity x =
  if RefUsage.is_nullable x then MemoryContext.Nullable else Valid

module MakeVarUsage(V : MemVar.VarUsage) : MemVar.VarUsage =
struct
  let datatype = "VarUsage." ^ V.datatype

  let param x =
    let get_addr = Wp_parameters.InHeap.get in
    let get_ctxt = Wp_parameters.InCtxt.get in
    let get_refs = Wp_parameters.ByRef.get in
    let get_vars = Wp_parameters.ByValue.get in
    let open Cil_types in
    let module S = Datatype.String.Set in
    let open MemoryContext in
    if S.mem x.vname (get_addr ()) then ByAddr else
    if S.mem x.vname (get_ctxt ()) then InContext (validity x) else
    if S.mem x.vname (get_refs ()) then ByRef else
    if S.mem x.vname (get_vars ()) then ByValue else
      V.param x

  let iter = V.iter

end

(* -------------------------------------------------------------------------- *)
(* --- Static Proxy (no preliminary analysis)                             --- *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* --- RefUsage-based Proxies                                             --- *)
(* -------------------------------------------------------------------------- *)

let is_ptr x = Cil.isPointerType x.Cil_types.vtype
let is_fun_ptr x = Cil.isFunctionType x.Cil_types.vtype
let is_formal_ptr x = x.Cil_types.vformal && is_ptr x
let is_init kf x =
  Globals.is_entry_point ~when_lib_entry:false kf ||
  Wp_parameters.AliasInit.get () ||
  ( Wp_parameters.Init.get () && Cil.isGlobalInitConst x )

let refusage_param ~byref ~context x =
  let kf,init = match WpContext.get_scope () with
    | WpContext.Global -> None , false
    | WpContext.Kf kf -> Some kf , is_init kf x in
  match RefUsage.get ?kf ~init x with
  | RefUsage.NoAccess -> MemoryContext.NotUsed
  | RefUsage.ByAddr -> MemoryContext.ByAddr
  | RefUsage.ByValue ->
    if context && is_formal_ptr x then MemoryContext.InContext (validity x)
    else if is_ptr x && not (is_fun_ptr x) then MemoryContext.ByShift
    else MemoryContext.ByValue
  | RefUsage.ByRef ->
    if byref
    then
      if RefUsage.is_nullable x
      then MemoryContext.InContext Nullable
      else MemoryContext.ByRef
    else MemoryContext.ByValue
  | RefUsage.ByArray ->
    if context && is_formal_ptr x
    then MemoryContext.InArray (validity x)
    else MemoryContext.ByShift

let refusage_iter ?kf ~init f = RefUsage.iter ?kf ~init (fun x _usage -> f x)

module Var : MemVar.VarUsage =
struct
  let datatype = "Var"
  let param = refusage_param ~byref:false ~context:false
  let iter = refusage_iter
end

module Ref : MemVar.VarUsage =
struct
  let datatype = "Ref"
  let param = refusage_param ~byref:true ~context:false
  let iter = refusage_iter
end

module Caveat : MemVar.VarUsage =
struct
  let datatype = "Caveat"
  let param = refusage_param ~byref:true ~context:true
  let iter = refusage_iter
end

(* -------------------------------------------------------------------------- *)
(* --- Generator & Model                                                  --- *)
(* -------------------------------------------------------------------------- *)

(* Each model must be instanciated statically because of registered memory
   models identifiers and Frama-C states *)

module Register(V : MemVar.VarUsage)(M : Sigs.Model)
  = MemVar.Make(MakeVarUsage(V))(M)

module Model_Hoare_Raw = Register(MemVar.Raw)(MemEmpty)
module Model_Hoare_Ref = Register(Ref)(MemEmpty)
module Model_Typed_Var = Register(Var)(MemTyped)
module Model_Typed_Ref = Register(Ref)(MemTyped)
module Model_Caveat = Register(Caveat)(MemTyped)

module MemVal = MemVal.Make(MemVal.Eva)

module MakeCompiler(M:Sigs.Model) =
struct
  module M = M
  module C = CodeSemantics.Make(M)
  module L = LogicSemantics.Make(M)
  module A = LogicAssigns.Make(M)(L)
end

module Comp_Region = MakeCompiler(Register(MemVar.Static)(MemRegion))
module Comp_MemZeroAlias = MakeCompiler(MemZeroAlias)
module Comp_Hoare_Raw = MakeCompiler(Model_Hoare_Raw)
module Comp_Hoare_Ref = MakeCompiler(Model_Hoare_Ref)
module Comp_MemTyped = MakeCompiler(MemTyped)
module Comp_Typed_Var = MakeCompiler(Model_Typed_Var)
module Comp_Typed_Ref = MakeCompiler(Model_Typed_Ref)
module Comp_Caveat = MakeCompiler(Model_Caveat)
module Comp_MemVal = MakeCompiler(MemVal)


let compiler mheap mvar : (module Sigs.Compiler) =
  match mheap , mvar with
  | ZeroAlias , _     -> (module Comp_MemZeroAlias)
  | Region , _        -> (module Comp_Region)
  | _    ,   Caveat   -> (module Comp_Caveat)
  | Hoare , (Raw|Var) -> (module Comp_Hoare_Raw)
  | Hoare ,   Ref     -> (module Comp_Hoare_Ref)
  | Typed _ , Raw     -> (module Comp_MemTyped)
  | Typed _ , Var     -> (module Comp_Typed_Var)
  | Typed _ , Ref     -> (module Comp_Typed_Ref)
  | Eva, _            -> (module Comp_MemVal)

(* -------------------------------------------------------------------------- *)
(* --- Tuning                                                             --- *)
(* -------------------------------------------------------------------------- *)

let configure_mheap = function
  | Hoare -> MemEmpty.configure ()
  | ZeroAlias -> MemZeroAlias.configure ()
  | Region -> MemRegion.configure ()
  | Eva -> MemVal.configure ()
  | Typed p ->
    let rollback_memtyped = MemTyped.configure () in
    let orig_memtyped_pointer = Context.push MemTyped.pointer p in
    let rollback () =
      rollback_memtyped () ;
      Context.pop MemTyped.pointer orig_memtyped_pointer
    in
    rollback

let configure_driver setup driver () =
  let rollback_mheap = configure_mheap setup.mheap in
  let rollback_cint = Cint.configure setup.cint in
  let rollback_cfloat = Cfloat.configure setup.cfloat in
  let old_driver = Context.push LogicBuiltins.driver driver in
  let rollback () =
    Context.pop LogicBuiltins.driver old_driver ;
    rollback_cfloat () ;
    rollback_cint () ;
    rollback_mheap ()
  in
  rollback

(* -------------------------------------------------------------------------- *)
(* --- Access                                                             --- *)
(* -------------------------------------------------------------------------- *)

module COMPILERS = Map.Make
    (struct
      type t = setup * driver
      let compare (s,d) (s',d') =
        let cmp = Stdlib.compare s s' in
        if cmp <> 0 then cmp else LogicBuiltins.compare d d'
    end)

let instances = ref (COMPILERS.empty : WpContext.model COMPILERS.t)

let instance setup driver =
  try COMPILERS.find (setup,driver) !instances
  with Not_found ->
    let id,descr = describe setup in
    let module CC = (val compiler setup.mheap setup.mvar) in
    let configure = configure_driver setup driver in
    let hypotheses = CC.M.hypotheses in
    let id,descr =
      if LogicBuiltins.is_default driver then id,descr
      else
        ( id ^ "_" ^ LogicBuiltins.id driver ,
          descr ^ " (Driver " ^ LogicBuiltins.descr driver ^ ")" )
    in
    let model = WpContext.register ~id ~descr ~configure ~hypotheses () in
    instances := COMPILERS.add (setup,driver) model !instances ; model

let ident s = fst (describe s)
let descr s = snd (describe s)

let split ~warning (m:string) : string list =
  let tk = ref [] in
  let buffer = Buffer.create 32 in
  let flush () =
    if Buffer.length buffer > 0 then
      begin
        tk := !tk @ [Buffer.contents buffer] ;
        Buffer.clear buffer ;
      end
  in
  String.iter
    (fun c ->
       match c with
       | 'A' .. 'Z' -> Buffer.add_char buffer c
       | '0' .. '9' -> Buffer.add_char buffer c
       | '_' | ',' | '@' | '+' | ' ' | '\t' | '\n' | '(' | ')' -> flush ()
       | _ -> warning (Printf.sprintf
                         "In model spec %S : unexpected character '%c'" m c)
    )
    (String.uppercase_ascii m) ;
  flush () ; !tk

let update_config ~warning m s = function
  | "ZEROALIAS" -> { s with mheap = ZeroAlias }
  | "REGION" -> { s with mheap = Region }
  | "HOARE" -> { s with mheap = Hoare }
  | "TYPED" -> { s with mheap = Typed MemTyped.Fits }
  | "CAST" -> { s with mheap = Typed MemTyped.Unsafe }
  | "NOCAST" -> { s with mheap = Typed MemTyped.NoCast }
  | "EVA" -> { s with mheap = Eva }
  | "CAVEAT" -> { s with mvar = Caveat }
  | "RAW" -> { s with mvar = Raw }
  | "REF" -> { s with mvar = Ref }
  | "VAR" -> { s with mvar = Var }
  | "INT" | "CINT" -> { s with cint = Cint.Machine }
  | "NAT" -> { s with cint = Cint.Natural }
  | "REAL" -> { s with cfloat = Cfloat.Real }
  | "FLOAT" | "CFLOAT" -> { s with cfloat = Cfloat.Float }
  | t -> warning (Printf.sprintf
                    "In model spec %S : unknown '%s' selector@." m t) ; s

let apply_config ~warning (s:setup) m : setup =
  List.fold_left (update_config ~warning m) s (split ~warning m)

let default =
  {
    mheap = Typed MemTyped.Fits ;
    mvar = Var ;
    cint = Cint.Machine ;
    cfloat = Cfloat.Float ;
  }

let abort msg = Wp_parameters.abort "%s" msg

let parse ?(default=default) ?(warning=abort) opts =
  List.fold_left (apply_config ~warning) default opts
