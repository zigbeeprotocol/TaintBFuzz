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

(** Information about version of Frama-C.
    The body of this module is generated from Makefile. *)

val version: string
(** Frama-C Version identifier. *)

val codename: string
(** Frama-C version codename.
    @since 18.0-Argon *)

val version_and_codename: string
(** Frama-C version and codename.
    @since 18.0-Argon *)

val major_version: int
(** Frama-C major version number.
    @since 19.0-Potassium *)

val minor_version: int
(** Frama-C minor version number.
    @since 19.0-Potassium *)

val is_gui: bool ref
(** Is the Frama-C GUI running?
    @since Beryllium-20090601-beta1 *)

val lablgtk: string
(** Name of the lablgtk version against which Frama-C has been compiled.
    blank if only command-line mode is available. *)

val ocamlc: string
(** Name of the bytecode compiler.
    @since Boron-20100401 *)

val ocamlopt: string
(** Name of the native compiler.
    @since Boron-20100401 *)

val ocaml_wflags: string
(** Warning flags used when compiling Frama-C.
    @since Chlorine-20180501 *)

val datadir: Filepath.Normalized.t
(** Directory where architecture independent files are.
    Main directory, use {!datadirs} for the others *)

val datadirs: Filepath.Normalized.t list
(** Directories where architecture independent files are in order of
    priority.
    @since 19.0-Potassium *)

val framac_libc: Filepath.Normalized.t
(** Directory where Frama-C libc headers are.
    @since 19.0-Potassium *)

val libdir: Filepath.Normalized.t
(** Directory where the Frama-C kernel library is.
    @since Beryllium-20090601-beta1 *)

val plugin_dir: Filepath.Normalized.t list
(** Directory where the Frama-C dynamic plug-ins are. *)

val plugin_path: string
(** The colon-separated concatenation of [plugin_dir].
    @since Magnesium-20151001 *)

val compilation_unit_names: string list
(** List of names of all kernel compilation units.
    @since Boron-20100401 *)

val library_names: string list
(** List of linked libraries.
    @since Magnesium-20151001 *)

val preprocessor: string
(** Name of the default command to call the preprocessor.
    If the CPP environment variable is set, use it
    else use the built-in default from autoconf. Usually this is
    "gcc -C -E -I."
    @since Oxygen-20120901 *)

val using_default_cpp: bool
(** whether the preprocessor command is the one defined at configure time
    or the result of taking a CPP environment variable, in case it differs
    from the configure-time command.

    @since Phosphorus-20170501-beta1 *)

val preprocessor_is_gnu_like: bool
(** whether the default preprocessor accepts the same options as gcc
    (i.e. is either gcc or clang), when this is the case, the default
    command line for pre-processing contains more options.
    @since Sodium-20150201
*)

val preprocessor_supported_arch_options: string list
(** architecture-related options (e.g. -m32) known to be supported by
    the default preprocessor. Used to match preprocessor commands to
    selected machdeps.
    @since Phosphorus-20170501-beta1
*)

val preprocessor_keep_comments: bool
(** [true] if the default preprocessor selected during compilation is
    able to keep comments (hence ACSL annotations) in its output.
    @since Neon-rc3
*)

val dot: string option
(** Dot command name.
    @return [None] if `dot' is not installed.
    @since Carbon-20101201 *)

(*
  Local Variables:
  compile-command: "make -C ../../.."
  End:
*)
