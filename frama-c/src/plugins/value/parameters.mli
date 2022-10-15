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

module ForceValues: Parameter_sig.With_output

module EnumerateCond: Parameter_sig.Bool
module OracleDepth: Parameter_sig.Int
module ReductionDepth: Parameter_sig.Int

module Domains: Parameter_sig.String_set
module DomainsFunction: Parameter_sig.Multiple_map
  with type key = string
   and type value = Domain_mode.function_mode

module EqualityCall: Parameter_sig.String
module EqualityCallFunction:
  Parameter_sig.Map with type key = Cil_types.kernel_function
                     and type value = string

module OctagonCall: Parameter_sig.Bool

module TracesUnrollLoop: Parameter_sig.Bool
module TracesUnifyLoop: Parameter_sig.Bool
module TracesDot: Parameter_sig.Filepath
module TracesProject: Parameter_sig.Bool

module MultidimSegmentLimit: Parameter_sig.Int
module MultidimDisjunctiveInvariants: Parameter_sig.Bool

module AutomaticContextMaxDepth: Parameter_sig.Int
module AutomaticContextMaxWidth: Parameter_sig.Int

module AllRoundingModesConstants: Parameter_sig.Bool

module NoResultsDomains: Parameter_sig.String_set
module NoResultsFunctions: Parameter_sig.Fundec_set
module ResultsAll: Parameter_sig.Bool

module JoinResults: Parameter_sig.Bool

module WarnSignedConvertedDowncast: Parameter_sig.Bool
module WarnPointerSubstraction: Parameter_sig.Bool
module WarnCopyIndeterminate: Parameter_sig.Kernel_function_set

module DescendingIteration: Parameter_sig.String
module HierarchicalConvergence: Parameter_sig.Bool
module WideningDelay: Parameter_sig.Int
module WideningPeriod: Parameter_sig.Int

module RecursiveUnroll: Parameter_sig.Int

module SemanticUnrollingLevel: Parameter_sig.Int
module SlevelFunction:
  Parameter_sig.Map with type key = Cil_types.kernel_function
                     and type value = int
module SlevelMergeAfterLoop: Parameter_sig.Kernel_function_set

module MinLoopUnroll : Parameter_sig.Int
module AutoLoopUnroll : Parameter_sig.Int
module DefaultLoopUnroll : Parameter_sig.Int
module HistoryPartitioning : Parameter_sig.Int
module ValuePartitioning : Parameter_sig.String_set
module SplitLimit : Parameter_sig.Int
module InterproceduralSplits : Parameter_sig.Bool
module InterproceduralHistory : Parameter_sig.Bool

module ArrayPrecisionLevel: Parameter_sig.Int

module AllocatedContextValid: Parameter_sig.Bool
module InitializationPaddingGlobals: Parameter_sig.String

module Numerors_Real_Size : Parameter_sig.Int
module Numerors_Mode : Parameter_sig.String

module UndefinedPointerComparisonPropagateAll: Parameter_sig.Bool
module WarnPointerComparison: Parameter_sig.String

module ReduceOnLogicAlarms: Parameter_sig.Bool
module InitializedLocals: Parameter_sig.Bool

module UsePrototype: Parameter_sig.Kernel_function_set

module SkipLibcSpecs: Parameter_sig.Bool

module RmAssert: Parameter_sig.Bool

module LinearLevel: Parameter_sig.Int
module LinearLevelFunction:
  Parameter_sig.Map with type key = Cil_types.kernel_function
                     and type value = int

module BuiltinsOverrides:
  Parameter_sig.Map with type key = Cil_types.kernel_function
                     and type value = string
module BuiltinsAuto: Parameter_sig.Bool
module BuiltinsList: Parameter_sig.Bool
module SplitReturnFunction:
  Parameter_sig.Map with type key = Cil_types.kernel_function
                     and type value = Split_strategy.t
module SplitGlobalStrategy: State_builder.Ref with type data = Split_strategy.t

module ValShowProgress: Parameter_sig.Bool
module ValShowPerf: Parameter_sig.Bool
module ValPerfFlamegraphs: Parameter_sig.Filepath
module ShowSlevel: Parameter_sig.Int
module PrintCallstacks: Parameter_sig.Bool
module ReportRedStatuses: Parameter_sig.Filepath
module NumerorsLogFile: Parameter_sig.Filepath

module MemExecAll: Parameter_sig.Bool


module InterpreterMode: Parameter_sig.Bool
module StopAtNthAlarm: Parameter_sig.Int


(** Dynamic allocation *)

module AllocBuiltin: Parameter_sig.String
module AllocFunctions: Parameter_sig.String_set
module AllocReturnsNull: Parameter_sig.Bool
module MallocLevel: Parameter_sig.Int

(** Meta-option *)
module Precision: Parameter_sig.Int

(* Automatically sets some parameters according to the meta-option
   -eva-precision. *)
val configure_precision: unit -> unit


val parameters_correctness: Typed_parameter.t list
val parameters_tuning: Typed_parameter.t list

(** Registers available cvalue builtins for the -eva-builtin option. *)
val register_builtin: string -> unit

(** Registers available domain names for the -eva-domains option. *)
val register_domain: name:string -> descr:string -> unit

[@@@ api_start]

(** Configuration of the analysis. *)

(** Returns the list (name, descr) of currently enabled abstract domains. *)
val enabled_domains: unit -> (string * string) list

(** [use_builtin kf name] instructs the analysis to use the builtin [name]
    to interpret calls to function [kf].
    Raises [Not_found] if there is no builtin of name [name]. *)
val use_builtin: Cil_types.kernel_function -> string -> unit

(** [use_global_value_partitioning vi] instructs the analysis to use
    value partitioning on the global variable [vi]. *)
val use_global_value_partitioning: Cil_types.varinfo -> unit
[@@@ api_end]
