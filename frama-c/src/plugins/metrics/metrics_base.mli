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

(** Tag functions handling html tags for Format *)
val html_stag_functions : Format.formatter_stag_functions;;

(** mk_hdr [level] [ppf] [hdr_strg] produces a title from [hdr_strg] with an
    underline of the same length.
    The character of the underline is set according to [level]:
    - level 1 headers are underlined by '='
    - level 2 headers by '-'
    - level 3 headers by '~'

    This function is supposed to follow reStructuredText's conventions.
*)
val mk_hdr : int -> Format.formatter -> string -> unit;;

module OptionKf : Datatype.S_with_collections with type t = Kernel_function.t option

module BasicMetrics : sig
  (** Simple type of metrics. *)
  type t = {
    cfile_name : Datatype.Filepath.t ;    (** Filename *)
    cfunc : OptionKf.t; (** Function name if applicable
                            ([None] for global metrics) *)
    cslocs: int ;            (** Lines of code w.r.t. statements *)
    cifs: int ;              (** If / cases of switch *)
    cloops: int ;            (** Loops: for, while, do...while *)
    ccalls: int ;            (** Function calls *)
    cgotos: int ;            (** Gotos *)
    cassigns: int ;          (** Assignments *)
    cexits: int ;            (** Exit points: return *)
    cfuncs: int ;            (** Functions defined: 1 in the case of a single
                                 function, possibly more for a file.*)
    cptrs: int ;             (** Access to pointers *)
    cdecision_points: int ;  (** Decision points of the program: ifs,
                                 switch cases, exception handlers, ... *)
    cglob_vars: int;         (** Global variables *)
    ccyclo: int;             (** Cyclomatic complexity *)
  }


  (** Helpers for metrics purposes for single increment steps *)
  val incr_funcs : t -> t ;;
  val incr_slocs : t -> t ;;
  val incr_ptrs : t -> t ;;
  val incr_ifs : t -> t ;;
  val incr_dpoints : t -> t ;;
  val incr_loops : t -> t ;;
  val incr_gotos : t -> t ;;
  val incr_exits : t -> t ;;
  val incr_assigns : t -> t ;;
  val incr_calls : t -> t ;;
  val incr_glob_vars : t -> t ;;

  val set_cyclo : t -> int -> t ;;

  (** Update a reference from a pure functional function.
      Used in particular in combination with helper functions above.
  *)
  val apply_then_set : (t -> t) -> t ref -> unit ;;

  (** Initial empty values for metrics computing. *)
  val empty_metrics: t;;

  (** Compute cyclomatic complexity from base_metrics record type. *)
  val compute_cyclo: t -> int;;

  (** Matrix-like representation of the record in "Title: value" style *)
  val to_list : t -> string list list ;;

  (** Pretty printers for base metrics as text or html. *)
  val pp_base_metrics: Format.formatter -> t -> unit;;
  val pp_base_metrics_as_html_row: Format.formatter -> t -> unit;;

end
;;

(** Local varinfo map and set where the comparison function is the
    lexicographic one on their respective names. *)
module VInfoMap: Map.S with type key = Cil_types.varinfo
module VInfoSet: Set.S with type elt = Cil_types.varinfo
;;


(** Pretty print a varinfo set, with some additional information about the
    varinfo. *)
val pretty_set : Format.formatter -> int VInfoMap.t -> unit
;;

val pretty_extern_vars: Format.formatter -> VInfoSet.t -> unit

(** Build a JSON list with the varinfos in [m], each as a JSON object with
    the varinfo name as key and additional attributes as values. *)
val json_of_varinfo_map : int VInfoMap.t -> Yojson.t

(** Handling entry points informations *)
val number_entry_points : int VInfoMap.t -> int
;;

val pretty_entry_points :
  Format.formatter -> int VInfoMap.t -> unit
;;

val json_of_entry_points : int VInfoMap.t -> Yojson.t

(** Get the filename where the definition of a varinfo occurs *)
val file_of_vinfodef: Cil_types.varinfo -> Datatype.Filepath.t;;

(** Get the filename containing the function definition *)
val file_of_fundef: Cil_types.fundec -> Datatype.Filepath.t;;


val extract_fundef_name: Cabs.single_name -> string;;
val kf_of_cabs_name: Cabs.single_name -> Kernel_function.t;;
val get_filename: Cabs.definition -> Datatype.Filepath.t;;

(** Type of the generated report file.
    Automatically set according to the file extension.
*)
type output_type =
  | Html
  | Text
  | Json
;;

(** get_file_type [extension] sets the output type according to [extension].
    Raises an error if [extension] is not among supported extensions or is empty.
*)
val get_file_type: Filepath.Normalized.t -> output_type;;

(** consider_function [vinfo] returns false if the varinfo is not a function we
    are interested in.
    For example, builtins should not be part of the analysis and return false.
    If [libc] is false, do not consider functions from the Frama-C libc.
    Skip them using this auxiliary function.
*)
val consider_function: libc:bool -> Cil_types.varinfo -> bool

(** [consider_variable vinfo] returns false if the varinfo is not an object
    variable we are interested in.
    If [libc] is false, do not consider variables from the Frama-C libc.
*)
val consider_variable: libc:bool -> Cil_types.varinfo -> bool

(** Convert float to string with the following convention:
    - if the float is an integer (ie, it has no digits after the decimal point),
      print it as such;
    - otherwise, print the first two digits after the decimal point.
*)
val float_to_string : float -> string ;;
