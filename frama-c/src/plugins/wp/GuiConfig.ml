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

(* ------------------------------------------------------------------------ *)
(* ---  Prover List in Configuration                                    --- *)
(* ------------------------------------------------------------------------ *)

module S = Why3.Whyconf.Sprover
module M = Why3.Whyconf.Mprover

class provers =
  object(self)
    inherit [S.t] Wutil.selector S.empty

    initializer
      begin
        (* select automatically the provers set on the command line *)
        let cmdline =
          match Wp_parameters.Provers.get () with
          | [] -> [ "alt-ergo" ]
          | prvs -> prvs
        in
        let selection = List.fold_left
            (fun acc e ->
               match Why3Provers.find_opt e with
               | None -> acc
               | Some p -> S.add p acc)
            S.empty cmdline
        in
        self#set selection ;
      end

  end

(* ------------------------------------------------------------------------ *)
(* ---  WP Provers Configuration Panel                                  --- *)
(* ------------------------------------------------------------------------ *)

class dp_chooser
    ~(main:Design.main_window_extension_points)
    ~(provers:provers)
  =
  let dialog = new Wpane.dialog
    ~title:"Why3 Provers"
    ~window:main#main_window
    ~resize:false () in
  let array = new Wpane.warray () in
  object(self)

    val mutable mainstream = true
    val mutable selected = M.empty

    method private enable dp e =
      selected <- M.add dp e selected

    method private lookup dp =
      try M.find dp selected with Not_found -> false

    method private entry dp =
      let text = Why3Provers.title dp in
      let sw = new Widget.switch () in
      let lb = new Widget.label ~align:`Left ~text () in
      sw#set (self#lookup dp) ;
      sw#connect (self#enable dp) ;
      let hbox = GPack.hbox ~spacing:10 ~homogeneous:false () in
      hbox#pack ~expand:false sw#coerce ;
      hbox#pack ~expand:true lb#coerce ;
      (object
        method widget = hbox#coerce
        method update () = sw#set (self#lookup dp)
        method delete () = ()
      end)

    method private configure dps =
      begin
        array#set (Why3.Whyconf.Sprover.elements dps) ;
        array#update () ;
      end

    method private provers =
      let filter p =
        self#lookup p || not mainstream || Why3Provers.is_mainstream p
      in S.filter filter (Why3Provers.provers_set ())

    method private filter () =
      begin
        mainstream <- not mainstream ;
        self#configure self#provers ;
      end

    method private apply () =
      provers#set
        (M.map_filter
           (function
             | true -> Some ()
             | false -> None)
           selected)

    method run () =
      selected <- M.empty ;
      let dps = self#provers in
      let sel = provers#get in
      selected <- M.merge
          (fun _ avail enab ->
             match avail, enab with
             | None, _ -> None
             | Some (), Some () -> Some true
             | Some (), None -> Some false)
          dps sel;
      self#configure dps ;
      dialog#run ()

    initializer
      begin
        dialog#button ~action:(`ACTION self#filter) ~label:"Filter"
          ~tooltip:"Switch to main stream / alternative solvers" () ;
        dialog#button ~action:(`CANCEL) ~label:"Cancel" () ;
        dialog#button ~action:(`APPLY) ~label:"Apply" () ;
        array#set_entry self#entry ;
        dialog#add_block array#coerce ;
        dialog#on_value `APPLY self#apply ;
      end

  end

(* ------------------------------------------------------------------------ *)
