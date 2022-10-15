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

(** This module is meant to build C or ACSL expressions in a unified way.
    Compared to "classic" Cil functions it also avoid the necessity to provide
    a location everywhere.
*)

module Type :
sig
  exception NotACType

  type ('value,'shape) typ

  (* Logic types *)
  val of_ltyp : Cil_types.logic_type -> (unit,unit) typ
  val integer : (unit,unit) typ
  val real : (unit,unit) typ

  (* C base types *)
  val of_ctyp : Cil_types.typ -> ('v,'v) typ
  val void : ('v,'v) typ
  val bool : ('v,'v) typ
  val char : ('v,'v) typ
  val schar : ('v,'v) typ
  val uchar : ('v,'v) typ
  val int : ('v,'v) typ
  val unit : ('v,'v) typ
  val short : ('v,'v) typ
  val ushort : ('v,'v) typ
  val long : ('v,'v) typ
  val ulong : ('v,'v) typ
  val longlong : ('v,'v) typ
  val ulonglong : ('v,'v) typ
  val float : ('v,'v) typ
  val double : ('v,'v) typ
  val longdouble : ('v,'v) typ

  val ptr : ('v,'s) typ -> ('v,'v) typ
  val array : ?size:int -> ('v,'s) typ -> ('v,'s list) typ

  (* Attributes *)
  val attribute : ('v,'s) typ -> string -> Cil_types.attrparam list
    -> ('v,'s) typ
  val const : ('v,'s) typ -> ('v,'s) typ
  val stdlib_generated : ('v,'s) typ -> ('v,'s) typ

  (* Conversion *)
  val cil_typ : ('v,'s) typ -> Cil_types.typ
  val cil_logic_type : ('v,'s) typ -> Cil_types.logic_type
end


(* --- C & Logic expressions builder --- *)

module Exp :
sig
  include module type of Type

  type const'
  type var'
  type lval'
  type exp'
  type init'

  type label
  type const = [ `const of const' ]
  type var = [ `var of var' ]
  type lval = [  var | `lval of lval' ]
  type exp = [ const | lval | `exp of exp' ]
  type init = [ exp | `init of init']

  val pretty : Format.formatter -> [init | `none] -> unit

  val none : [> `none]

  (* Labels *)

  val here : label
  val old : label
  val pre : label
  val post : label
  val loop_entry : label
  val loop_current : label
  val program_init : label

  (* Constants *)

  val of_constant : Cil_types.constant -> [> const]
  val of_int : int -> [> const]
  val of_integer : Integer.t -> [> const]
  val zero : [> const]
  val one : [> const]

  (* Lvalues *)

  val var : Cil_types.varinfo -> [> var]
  val of_lval : Cil_types.lval -> [> lval]

  (* Expressions *)

  exception EmptyList

  val of_exp : Cil_types.exp -> [> exp]
  val of_exp_copy : Cil_types.exp -> [> exp]
  val unop : Cil_types.unop -> [< exp] -> [> exp]
  val neg : [< exp] -> [> exp]
  val lognot : [< exp] -> [> exp]
  val bwnot : [< exp] -> [> exp]
  val succ : [< exp] -> [> exp] (* e + 1 *)
  val add_int : [< exp] -> int -> [> exp] (* e + i *)
  val binop : Cil_types.binop -> [< exp] -> [< exp] -> [> exp]
  val add : [< exp] -> [< exp] -> [> exp]
  val sub : [< exp] -> [< exp] -> [> exp]
  val mul : [< exp] -> [< exp] -> [> exp]
  val div : [< exp] -> [< exp] -> [> exp]
  val modulo : [< exp] -> [< exp] -> [> exp]
  val shiftl : [< exp] -> [< exp] -> [> exp]
  val shiftr : [< exp] -> [< exp] -> [> exp]
  val lt : [< exp] -> [< exp] -> [> exp]
  val gt : [< exp] -> [< exp] -> [> exp]
  val le : [< exp] -> [< exp] -> [> exp]
  val ge : [< exp] -> [< exp] -> [> exp]
  val eq : [< exp] -> [< exp] -> [> exp]
  val ne : [< exp] -> [< exp] -> [> exp]
  val logor : [< exp] -> [< exp] -> [> exp]
  val logand : [< exp] -> [< exp] -> [> exp]
  val logor_list : [< exp] list -> exp
  val logand_list : [< exp] list -> exp
  val bwand : [< exp] -> [< exp] -> [> exp]
  val bwor : [< exp] -> [< exp] -> [> exp]
  val bwxor : [< exp] -> [< exp] -> [> exp]
  val cast : ('v,'s) typ -> [< exp] -> [> exp]
  val cast' : Cil_types.typ -> [< exp] -> [> exp]
  val addr : [< lval] -> [> exp]
  val mem : [< exp] -> [> lval]
  val index : [< lval] -> [< exp] -> [> lval]
  val field : [< lval] -> Cil_types.fieldinfo -> [> lval]
  val fieldnamed : [< lval] -> string -> [> lval]

  val result : [> lval]
  val term : Cil_types.term -> [> exp]
  val range :  [< exp | `none] -> [< exp | `none] -> [> exp]
  val whole : [> exp] (* Whole range, i.e. .. *)
  val whole_right : [> exp] (* Whole range right side, i.e. 0.. *)
  val app : Cil_types.logic_info -> label list -> [< exp] list -> [> exp]

  val object_pointer : ?at:label -> [< exp] -> [> exp]
  val valid : ?at:label -> [< exp] -> [> exp]
  val valid_read : ?at:label -> [< exp] -> [> exp]
  val initialized : ?at:label -> [< exp] -> [> exp]
  val dangling : ?at:label -> [< exp] -> [> exp]
  val allocable : ?at:label -> [< exp] -> [> exp]
  val freeable : ?at:label -> [< exp] -> [> exp]
  val fresh : label -> label -> [< exp] -> [< exp] -> [> exp]

  val of_init : Cil_types.init -> [> init]
  val compound : Cil_types.typ -> init list -> [> init]
  val values : (init,'values) typ -> 'values -> init


  (* Redefined operators *)

  val (+) : [< exp] -> [< exp] -> [> exp]
  val (-) : [< exp] -> [< exp] -> [> exp]
  val ( * ) : [< exp] -> [< exp] -> [> exp]
  val (/) : [< exp] -> [< exp] -> [> exp]
  val (%) : [< exp] -> [< exp] -> [> exp]
  val (<<) : [< exp] -> [< exp] -> [> exp]
  val (>>) : [< exp] -> [< exp] -> [> exp]
  val (<) : [< exp] -> [< exp] -> [> exp]
  val (>) : [< exp] -> [< exp] -> [> exp]
  val (<=) : [< exp] -> [< exp] -> [> exp]
  val (>=) : [< exp] -> [< exp] -> [> exp]
  val (==) : [< exp] -> [< exp] -> [> exp]
  val (!=) : [< exp] -> [< exp] -> [> exp]
  val (--) : [< exp] -> [< exp] -> [> exp]

  (* Export CIL objects from built expressions *)

  exception LogicInC of exp
  exception CInLogic of exp
  exception NotATerm of exp
  exception NotAPredicate of exp
  exception NotAFunction of Cil_types.logic_info
  exception Typing_error of string

  val cil_logic_label : label -> Cil_types.logic_label
  val cil_constant : [< const] -> Cil_types.constant
  val cil_varinfo : [< var] -> Cil_types.varinfo
  val cil_lval : loc:Cil_types.location -> [< lval] -> Cil_types.lval
  val cil_exp : loc:Cil_types.location -> [< exp] -> Cil_types.exp
  val cil_term_lval : loc:Cil_types.location -> ?restyp:Cil_types.typ ->
    [< lval] -> Cil_types.term_lval
  val cil_term : loc:Cil_types.location -> ?restyp:Cil_types.typ ->
    [< exp] -> Cil_types.term
  val cil_iterm : loc:Cil_types.location -> ?restyp:Cil_types.typ ->
    [< exp] -> Cil_types.identified_term
  val cil_pred : loc:Cil_types.location -> ?restyp:Cil_types.typ ->
    [< exp] -> Cil_types.predicate
  val cil_ipred : loc:Cil_types.location -> ?restyp:Cil_types.typ ->
    [< exp] -> Cil_types.identified_predicate
  val cil_init : loc:Cil_types.location -> [< init] -> Cil_types.init

  val cil_typeof : [< var] -> Cil_types.typ
end


(* --- Pure builder --- *)

module Pure :
sig
  include module type of Exp

  type instr'
  type stmt'

  type instr = [ `instr of instr' ]
  type stmt = [ instr | `stmt of stmt' ]

  (* Instructions *)
  val of_instr : Cil_types.instr -> [> instr]
  val skip : [> instr]
  val assign : [< lval] -> [< exp] -> [> instr]
  val incr : [< lval] -> [> instr]
  val call : [< lval | `none] -> [< exp] -> [< exp] list -> [> instr]

  (* Statements *)
  val of_stmtkind : Cil_types.stmtkind -> [> stmt]
  val of_stmt : Cil_types.stmt -> [> stmt]
  val of_stmts : Cil_types.stmt list -> [> stmt]
  val block : [< stmt] list -> [> stmt]
  val ghost : [< stmt] -> [> stmt]

  val cil_instr : loc:Cil_types.location -> instr -> Cil_types.instr
  val cil_stmtkind : loc:Cil_types.location -> stmt -> Cil_types.stmtkind
  val cil_stmt : loc:Cil_types.location -> stmt -> Cil_types.stmt

  (* Operators *)
  val (:=) : [< lval] -> [< exp] -> [> instr] (* assign *)
  val (+=) : [< lval] -> [< exp] -> [> instr]
  val (-=) : [< lval] -> [< exp] -> [> instr]
end


(* --- Stateful builder --- *)

exception WrongContext of string

module type T =
sig
  val loc : Cil_types.location
end

module Stateful (Location : T) :
sig
  include module type of Exp

  (* Functions *)
  val open_function : ?ghost:bool -> ?vorig_name:string -> string -> [> var]
  val set_return_type : ('s,'v) typ -> unit
  val set_return_type' : Cil_types.typ -> unit
  val add_attribute : Cil_types.attribute -> unit
  val add_new_attribute : string -> Cil_types.attrparam list -> unit
  val add_stdlib_generated : unit -> unit
  val finish_function : ?register:bool -> unit -> Cil_types.global
  val finish_declaration : ?register:bool -> unit -> Cil_types.global

  (* Behaviors *)
  type source = [exp | `indirect of exp]
  val indirect: [< source] -> [> source]
  val assigns: [< exp] list -> [< exp | `indirect of [< exp]] list -> unit
  val requires: [< exp] -> unit
  val ensures: [< exp] -> unit

  (* Statements *)
  val of_stmtkind : Cil_types.stmtkind -> unit
  val of_stmt : Cil_types.stmt -> unit
  val of_stmts : Cil_types.stmt list -> unit
  val open_block : ?into:Cil_types.fundec -> ?ghost:bool -> unit -> unit
  val open_ghost : ?into:Cil_types.fundec -> unit -> unit
  val open_switch : ?into:Cil_types.fundec -> [< exp] -> unit
  val open_if : ?into:Cil_types.fundec -> [< exp] -> unit
  val open_else : unit -> unit
  val close : unit -> unit
  val finish_block : unit -> Cil_types.block
  val finish_instr_list : ?scope:Cil_types.block -> unit -> Cil_types.instr list
  val finish_stmt : unit -> Cil_types.stmt
  val case : [< exp] -> unit
  val break : unit -> unit
  val return : [< exp | `none] -> unit

  (* Variables *)
  val local : ?ghost:bool -> ?init:'v -> (init,'v) typ -> string -> [> var]
  val local' : ?ghost:bool -> ?init:init -> Cil_types.typ -> string -> [> var]
  val local_copy : ?ghost:bool -> ?suffix:string -> [< var] -> [> var]
  val parameter : ?ghost:bool -> ?attributes:Cil_types.attributes ->
    Cil_types.typ -> string -> [> var]

  (* Instructions *)
  val of_instr : Cil_types.instr -> unit
  val skip : unit -> unit
  val assign : [< lval] -> [< exp] -> unit
  val incr : [< lval] -> unit
  val call : [< lval | `none] -> [< exp] -> [< exp] list -> unit
  val pure : [< exp ] -> unit

  (* Operators *)
  val (:=) : [< lval] -> [< exp] -> unit (* assign *)
  val (+=) : [< lval] -> [< exp] -> unit
  val (-=) : [< lval] -> [< exp] -> unit
end
