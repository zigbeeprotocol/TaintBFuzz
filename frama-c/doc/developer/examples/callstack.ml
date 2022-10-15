(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  Contact CEA LIST for licensing.                                       *)
(*                                                                        *)
(**************************************************************************)

module P = 
  Plugin.Register
    (struct
      let name = "Callstack"
      let shortname = "Callstack"
      let help = "callstack library"
     end)

(* A callstack is a list of a pair (kf * stmt) where [kf] is the kernel
   function called at statement [stmt]. Building the datatype also creates the
   corresponding type value [ty]. *)
type callstack = (Kernel_function.t * Cil_datatype.Stmt.t) list

(* Implementation *)
let empty = []
let push kf stmt stack = (kf, stmt) :: stack
let pop = function [] -> [] | _ :: stack -> stack
let rec print = function 
  | [] -> P.feedback "" 
  | (kf, stmt) :: stack -> 
    P.feedback "function %a called at stmt %a" 
      Kernel_function.pretty kf
      Cil_datatype.Stmt.pretty stmt;
    print stack

(* Type values *)
let kf_ty = Kernel_function.ty
let stmt_ty = Cil_datatype.Stmt.ty

module D =
  Datatype.Make
    (struct
      type t = callstack
      let name = "Callstack.t"
      let reprs = [ empty; [ Kernel_function.dummy (), Cil.dummyStmt ] ]
      include Datatype.Serializable_undefined
     end)

(* Dynamic API registration *)
let register name ty =
  Dynamic.register ~plugin:"Callstack" ~journalize:false name ty

let empty = register "empty" D.ty empty
let push = register "push" (Datatype.func3 kf_ty stmt_ty D.ty D.ty) push
let pop = register "pop" (Datatype.func D.ty D.ty) pop
let print = register "print" (Datatype.func D.ty Datatype.unit) print
