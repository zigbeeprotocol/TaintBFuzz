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

let log_key = Self.register_category "unit-domain"

module Static = struct
  module D = struct
    include Datatype.Unit
    type state = t

    let name = "Unit domain"
    let log_category = log_key
    let structure = Abstract.Domain.Unit

    let top = ()
    let is_included _ _ = true
    let join _ _ = ()
    let widen _ _ _ _ = ()
    let narrow _ _ = `Value ()
  end

  include D
  include Domain_builder.Complete
      (struct
        include D
        let top = top
        let join = join
      end)
end

module Make
    (Value: Abstract_value.S)
    (Loc: Abstract_location.S)
= struct

  include Static
  type value = Value.t
  type location = Loc.location
  type origin

  let eval_top = `Value (Value.top, None), Alarmset.all
  let extract_expr ~oracle:_ _ _ _ = eval_top
  let extract_lval ~oracle:_ _ _ _ _ _ = eval_top

  let update _ _ = `Value ()
  let assign _ _ _ _ _ _ = `Value ()
  let assume _ _ _ _ _ = `Value ()
  let start_call _ _ _ _ _ = `Value ()
  let finalize_call _ _ _ ~pre:_ ~post:_ = `Value ()
  let show_expr _ _ _ _ = ()

  let logic_assign _ _ _ = ()

  let enter_scope _ _ _ = ()
  let leave_scope _ _ _ = ()

  let empty () = ()
  let initialize_variable _ _ ~initialized:_ _ _ = ()
  let initialize_variable_using_type _ _ _  = ()

  let relate _ _ () = Base.SetLattice.empty
end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
