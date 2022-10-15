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
(* --- Model Setup                                                        --- *)
(* -------------------------------------------------------------------------- *)

let user_setup () : Factory.setup =
  begin
    match Wp_parameters.Model.get () with
    | ["Runtime"] ->
      Wp_parameters.abort
        "Model 'Runtime' is no more available.@\nIt will be reintroduced \
         in a future release."
    | ["Logic"] ->
      Wp_parameters.warning ~once:true
        "Deprecated 'Logic' model.@\nUse 'Typed' with option '-wp-ref' \
         instead." ;
      {
        mheap = Factory.Typed MemTyped.Fits ;
        mvar = Factory.Ref ;
        cint = Cint.Natural ;
        cfloat = Cfloat.Real ;
      }
    | ["Store"] ->
      Wp_parameters.warning ~once:true
        "Deprecated 'Store' model.@\nUse 'Typed' instead." ;
      {
        mheap = Factory.Typed MemTyped.Fits ;
        mvar = Factory.Var ;
        cint = Cint.Natural ;
        cfloat = Cfloat.Real ;
      }
    | spec ->
      let setup = Factory.parse spec in
      let mref = match setup.mvar with
        | Caveat -> "caveat" | Ref -> "ref" | Raw | Var -> "" in
      if mref <> ""
      && RefUsage.has_nullable ()
      && not (Wp_parameters.RTE.is_set ())
      then
        Wp_parameters.warning ~current:false ~once:true
          "In %s model with nullable arguments, \
           -wp-(no)-rte shall be explicitly positioned."
          mref ;
      setup
  end

(* -------------------------------------------------------------------------- *)
(* --- WP Computer (main entry points)                                    --- *)
(* -------------------------------------------------------------------------- *)

let create
    ?dump
    ?(setup: Factory.setup option)
    ?(driver: Factory.driver option)
    () : Wpo.generator =
  let default f = function Some v -> v | None -> f () in
  let dump = default Wp_parameters.Dump.get dump in
  let driver = default Driver.load_driver driver in
  let setup = default user_setup setup in
  if dump
  then CfgGenerator.dumper setup driver
  else CfgGenerator.generator setup driver

(* -------------------------------------------------------------------------- *)
