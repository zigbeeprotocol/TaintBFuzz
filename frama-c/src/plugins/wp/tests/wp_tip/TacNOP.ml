open Wp.Tactical

(* ---------------------------------------------------------------------- *)
(* --- NOP Tactical                                                   --- *)
(* ---------------------------------------------------------------------- *)

class nop =
  object
    inherit Wp.Tactical.make
        ~id:"Wp.Test.NOP"
        ~title:"NOP"
        ~descr:"Does nothing."
        ~params:[]

    method select feedback (s : Wp.Tactical.selection) =
      match s with
      | Empty -> Not_applicable
      | Compose _
      | Multi _
      | Inside _
      | Clause _ ->
          feedback#set_title "NOP" ;
          feedback#set_descr "Does nothing; just for testing." ;
          Applicable (fun s -> ["Nop", s])

  end

let tactical = Wp.Tactical.export (new nop)

(* -------------------------------------------------------------------------- *)
