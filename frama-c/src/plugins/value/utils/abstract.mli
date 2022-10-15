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

(** Internal and External signature of abstractions used in the Eva engine. *)

(** Internal modules contains a [structure] value that describes the internal
    structure of the abstraction. This structure is used to automatically
    generate efficient accessors from a generic compound abstraction to specific
    leaf abstractions. *)

(** External modules export direct accessors to their leaf components.
    When a generic abstraction is a product of several specific abstractions,
    they allow interacting with each leaf abstraction identified by a key.
    Note that their behavior is undefined if an abstraction contains
    several times the same leaf module. *)

(** Key and structure for abstract values.
    See {!Structure} for more details. *)
module Value : sig
  include Structure.Shape
    with type 'a key = 'a Structure.Key_Value.key
     and type 'a data = (module Abstract_value.S with type t = 'a)

  module type Internal = sig
    include Abstract_value.S
    val structure: t structure
  end

  module type External = sig
    include Internal
    include Structure.External with type t := t
                                and type 'a key := 'a key
                                and type 'a data := 'a data
  end
end

(** Key and structure for abstract locations.
    See {!Structure} for more details. *)
module Location : sig
  include Structure.Shape
    with type 'a key = 'a Structure.Key_Location.key
     and type 'a data = (module Abstract_location.S with type location = 'a)

  module type Internal = sig
    include Abstract_location.S
    val structure: location structure
  end

  module type External = sig
    include Internal
    include Structure.External with type t := location
                                and type 'a key := 'a key
                                and type 'a data := 'a data
  end
end

(** Key and structure for abstract domains.
    See {!Structure} for more details. *)
module Domain : sig
  include Structure.Shape
    with type 'a key = 'a Structure.Key_Domain.key
     and type 'a data = (module Abstract_domain.S with type state = 'a)

  module type Internal = sig
    include Abstract_domain.S
    val structure: t structure
  end

  module type External = sig
    include Internal
    include Structure.External with type t := t
                                and type 'a key := 'a key
                                and type 'a data := 'a data

    (** Special accessors for the main cvalue domain. *)
    val get_cvalue: (t -> Cvalue.Model.t) option
    val get_cvalue_or_top: t -> Cvalue.Model.t
    val get_cvalue_or_bottom: t Lattice_bounds.or_bottom -> Cvalue.Model.t
  end
end
