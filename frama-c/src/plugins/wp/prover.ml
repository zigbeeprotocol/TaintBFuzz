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

open VCS

(* -------------------------------------------------------------------------- *)
(* --- Prover Implementation against Task API                             --- *)
(* -------------------------------------------------------------------------- *)

open Task
open Wpo

let dispatch ?(config=VCS.default) mode prover wpo =
  begin
    match prover with
    | Qed | Tactical -> Task.return VCS.no_result
    | Why3 prover ->
      let smoke = Wpo.is_smoke_test wpo in
      let kf = match Wpo.get_scope wpo with
        | Global -> None
        | Kf kf -> Some kf
      in
      ProverWhy3.prove
        ~timeout:(VCS.get_timeout ?kf ~smoke config)
        ~steplimit:(VCS.get_stepout config)
        ~mode ~prover wpo
  end

let started ?start wpo =
  match start with
  | None -> ()
  | Some f -> f wpo

let signal ?progress wpo msg =
  match progress with
  | None -> ()
  | Some f -> f wpo msg

let update ?result wpo prover res =
  Wpo.set_result wpo prover res ;
  match result with
  | None -> ()
  | Some f -> f wpo prover res

let run_prover wpo ?config ?(mode=Batch) ?progress ?result prover =
  signal ?progress wpo (VCS.name_of_prover prover) ;
  dispatch ?config mode prover wpo >>>
  fun status ->
  let res = match status with
    | Task.Result r -> r
    | Task.Canceled -> VCS.no_result
    | Task.Timeout t -> VCS.timeout t
    | Task.Failed exn -> VCS.failed (error exn)
  in
  let res = { res with solver_time = Wpo.qed_time wpo } in
  update ?result wpo prover res ;
  Task.return (VCS.is_valid res)

let simplify ?start ?result wpo =
  Task.call
    (fun wpo ->
       let r = Wpo.get_result wpo VCS.Qed in
       VCS.( r.verdict == Valid ) ||
       begin
         started ?start wpo ;
         if Wpo.reduce wpo then
           let time = qed_time wpo in
           let res = VCS.result ~time VCS.Valid in
           (update ?result wpo VCS.Qed res ; true)
         else false
       end)
    wpo

let prove wpo ?config ?mode ?start ?progress ?result prover =
  simplify ?start ?result wpo >>= fun succeed ->
  if succeed
  then Task.return true
  else (run_prover wpo ?config ?mode ?progress ?result prover)

let spawn wpo ~delayed
    ?config ?start ?progress ?result ?success ?pool provers =
  if provers<>[] then
    let monitor = match success with
      | None -> None
      | Some on_success ->
        Some
          begin function
            | None -> on_success wpo None
            | Some prover ->
              let r = Wpo.get_result wpo VCS.Qed in
              let prover =
                if VCS.( r.verdict == Valid ) then VCS.Qed else prover in
              on_success wpo (Some prover)
          end in
    let process (mode,prover) =
      prove wpo ?config ~mode ?start ?progress ?result prover in
    let all = Wp_parameters.RunAllProvers.get() in
    let smoke = Wpo.is_smoke_test wpo in
    ProverTask.spawn ?monitor ?pool ~all ~smoke
      (List.map
         (fun mp ->
            let prover = snd mp in
            let task = if delayed then Task.later process mp else process mp in
            prover , task
         ) provers)
  else
    let process = simplify ?start ?result wpo >>= fun ok ->
      begin
        match success with
        | None -> ()
        | Some on_success ->
          on_success wpo (if ok then Some VCS.Qed else None) ;
      end ;
      Task.return ()
    in
    let thread = Task.thread process in
    let server = ProverTask.server () in
    Task.spawn server ?pool thread

(* -------------------------------------------------------------------------- *)
