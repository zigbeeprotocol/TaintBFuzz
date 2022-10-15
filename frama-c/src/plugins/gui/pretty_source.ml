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

open Cil_types
open Gtk_helper
open Printer_tag

type localizable = Printer_tag.localizable =
  | PStmt of (kernel_function * stmt)
  | PStmtStart of (kernel_function * stmt)
  | PLval of (kernel_function option * kinstr * lval)
  | PExp of (kernel_function option * kinstr * exp)
  | PTermLval of (kernel_function option * kinstr * Property.t * term_lval)
  | PVDecl of (kernel_function option * kinstr * varinfo)
  (** Declaration and definition of variables and function. Check the type
      of the varinfo to distinguish between the various possibilities.
      If the varinfo is a global or a local, the kernel_function is the
      one in which the variable is declared. The [kinstr] argument is given
      for local variables with an explicit initializer. *)
  | PGlobal of global (** all globals but variable declarations and function
                          definitions. *)
  | PIP of Property.t

let kf_of_localizable = Printer_tag.kf_of_localizable
let ki_of_localizable = Printer_tag.ki_of_localizable
let varinfo_of_localizable = Printer_tag.varinfo_of_localizable

module Locs:sig
  type state
  val add: state -> int * int -> localizable -> unit
  val iter : state -> (int * int -> localizable -> unit) -> unit
  val create : unit -> state
  val clear : state -> unit
  val find : state -> int -> (int * int) * localizable
  val hilite : state -> unit
  val set_hilite : state -> (unit -> unit) -> unit
  val add_finalizer: state -> (unit -> unit) -> unit
  val size : state -> int
  val stmt_start: state -> stmt -> int
end
=
struct
  type state = { table : (int*int,localizable) Hashtbl.t;
                 mutable hiliter : unit -> unit;
                 mutable finalizers: (unit -> unit) list;
                 stmt_start: int Datatype.Int.Hashtbl.t
               (* mapping from sid to their offset in the buffer *);
               }

  let create () =
    {table = Hashtbl.create 97;
     hiliter = (fun () -> ());
     finalizers = [];
     stmt_start = Datatype.Int.Hashtbl.create 16;
    }

  let hilite state = state.hiliter ()

  let set_hilite state f =
    state.hiliter <- f

  let add_finalizer state f =
    state.finalizers <- f :: state.finalizers

  let finalize state =
    List.iter (fun f -> f ()) (List.rev state.finalizers)

  let clear state =
    finalize state;
    state.finalizers <- [];
    state.hiliter <- (fun () -> ());
    Hashtbl.clear state.table;
    Datatype.Int.Hashtbl.clear state.stmt_start;
  ;;

  (* Add a location range only if it is not already there.
     Visually only the innermost pretty printed entity is kept.
     For example: 'loop assigns x;' will be indexed as an assigns
     and not as a code annotation.
  *)
  let add state range = function
    | Printer_tag.PStmtStart(_,st) ->
      Datatype.Int.Hashtbl.add state.stmt_start st.sid (fst range)
    | localizable ->
      if not (Hashtbl.mem state.table range) then
        Hashtbl.add state.table range localizable

  let stmt_start state s =
    Datatype.Int.Hashtbl.find state.stmt_start s.sid

  let find state p =
    let best = ref None in
    let update ((b,e) as loc) sid =
      if b <= p && p <= e then
        match !best with
        | None -> best := Some (loc, sid)
        | Some ((b',e'),_) -> if e-b < e'-b' then best := Some (loc, sid)
    in
    Hashtbl.iter update state.table ;
    match !best with None -> raise Not_found | Some (loc,sid) -> loc, sid

  let iter state f =
    Hashtbl.iter f state.table

  let size state = Hashtbl.length state.table

end

let hilite state = Locs.hilite state
let stmt_start state = Locs.stmt_start state

module LocsArray:sig
  type t
  val create: Locs.state -> t
  val length : t -> int
  val get : t -> int -> (int * int) * localizable
  val find_next : t -> int -> (localizable -> bool) -> int
end
=
struct
  (* computes an ordered array containing all the elements of a Locs.state,
     the order (<) being such that loc1 < loc2 if either loc1 starts
     before loc2, or loc1 and loc2 start at the same position but
     loc1 spawns further than loc2.
  *)

  type t = ((int*int) * localizable option) array

  let create state =
    let arr = Array.make (Locs.size state) ((0,0), None) in
    let index = ref 0 in
    Locs.iter
      state
      (fun (pb,pe) v ->
         Array.set arr !index ((pb,pe), Some v) ;
         incr index
      )
    ;
    Array.sort
      (fun ((pb1,pe1),_) ((pb2,pe2),_) ->
         if (pb1 = pb2) then
           if (pe1 = pe2) then 0
           else
             (* most englobing comes first *)
             Stdlib.compare pe2 pe1
         else Stdlib.compare pb1 pb2
      ) arr
    ;
    arr

  let length arr = Array.length arr

  (* get loc at index i;
     raises Not_found if none exists *)
  let get arr i =
    if i >= Array.length arr then raise Not_found
    else
      match Array.get arr i with
      | ((_,_),None) -> raise Not_found
      | ((pb,pe),Some v) -> ((pb,pe),v)

  (* find the next loc in array starting at index i
     which satisfies the predicate;
     raises Not_found if none exists *)
  let find_next arr i predicate =
    let rec fnext i =
      let ((pb',_pe'),v) = get arr i in
      if predicate v then pb'
      else fnext (i+1)
    in fnext i

end

(* Set of callsite statements where preconditions must be unfolded. *)
let unfold_preconds = Cil_datatype.Stmt.Hashtbl.create 8

(* Fold or unfold the preconditions at callsite [stmt]. *)
let fold_preconds_at_callsite stmt =
  if Cil_datatype.Stmt.Hashtbl.mem unfold_preconds stmt
  then Cil_datatype.Stmt.Hashtbl.remove unfold_preconds stmt
  else Cil_datatype.Stmt.Hashtbl.replace unfold_preconds stmt ()

let are_preconds_unfolded stmt =
  Cil_datatype.Stmt.Hashtbl.mem unfold_preconds stmt

module Tag =
struct

  let hashtbl = Hashtbl.create 0
  let current = ref 0
  let charcode = function
    | PStmt _ -> 's'
    | PStmtStart _ -> 'k'
    | PLval _ -> 'l'
    | PExp _ -> 'e'
    | PTermLval _ -> 't'
    | PVDecl _ -> 'd'
    | PGlobal _ -> 'g'
    | PIP _ -> 'i'

  let create loc =
    incr current ;
    let tag = Printf.sprintf "guitag:%c%x" (charcode loc) !current in
    Hashtbl.replace hashtbl tag loc ; tag

  let get = Hashtbl.find hashtbl

end

module Printer = Printer_tag.Make(Tag)

exception Found of int*int

(* This function identifies two distinct localizable that happen to have
   the same location in the source code, typically because one of them
   is not printed. Feel free to add other heuristics if needed. *)
let equal_or_same_loc loc1 loc2 =
  let open Property in
  Localizable.equal loc1 loc2 ||
  match loc1, loc2 with
  | PIP (IPReachable {ir_kinstr=Kstmt s}), PStmt (_, s')
  | PStmt (_, s'), PIP (IPReachable {ir_kinstr=Kstmt s})
  | PIP (IPPropertyInstance {ii_stmt=s}), PStmt (_, s')
  | PStmt (_, s'), PIP (IPPropertyInstance {ii_stmt=s})
    when
      Cil_datatype.Stmt.equal s s' -> true
  | PIP (IPReachable {ir_kf=Some kf; ir_kinstr=Kglobal}),
    (PVDecl (_, _, vi) | PGlobal (GFun ({ svar = vi }, _)))
  | (PVDecl (_, _, vi) | PGlobal (GFun ({ svar = vi }, _))),
    PIP (IPReachable {ir_kf=Some kf;ir_kinstr=Kglobal})
    when Kernel_function.get_vi kf = vi
    -> true
  | _ -> false

let locate_localizable state loc =
  try
    Locs.iter
      state
      (fun (b,e) v -> if equal_or_same_loc v loc then raise (Found(b,e)));
    None
  with Found (b,e) -> Some (b,e)

let localizable_from_locs state ~file ~line =
  let r = ref [] in
  Locs.iter
    state
    (fun _ v ->
       let loc,_ = loc_of_localizable v in
       if line = loc.Filepath.pos_lnum && loc.Filepath.pos_path = file then
         r := v::!r);
  !r

let buffer_formatter state source =
  let starts = Stack.create () in
  let emit_open_tag s =
    let s = Extlib.format_string_of_stag s in
    (* Ignore tags that are not ours *)
    if Extlib.string_prefix "guitag:" s then
      Stack.push (source#end_iter#offset, Tag.get s) starts ;
    ""
  in
  let emit_close_tag s =
    let s = Extlib.format_string_of_stag s in
    (try
       if Extlib.string_prefix "guitag:" s then
         let (p,sid) = Stack.pop starts in
         Locs.add state (p, source#end_iter#offset) sid
     with Stack.Empty -> (* This should probably be a hard error *)
       Gui_parameters.error "empty stack in emit_tag");
    ""
  in
  let gtk_fmt = Gtk_helper.make_formatter source in
  Format.pp_set_tags gtk_fmt true;
  Format.pp_set_print_tags gtk_fmt false;
  Format.pp_set_mark_tags gtk_fmt true;
  let open Format in
  pp_set_formatter_stag_functions
    gtk_fmt {(pp_get_formatter_stag_functions gtk_fmt ())
             with
              mark_open_stag = emit_open_tag;
              mark_close_stag = emit_close_tag;};

  Format.pp_set_margin gtk_fmt 79;
  gtk_fmt

let display_source globals
    (source:GSourceView.source_buffer) ~(host:Gtk_helper.host)
    ~highlighter ~selector state =
  Locs.clear state;
  host#protect
    ~cancelable:false
    (fun () ->
       source#set_text "";
       source#remove_source_marks
         ~start:source#start_iter ~stop:source#end_iter ();
       let hiliter () =
         let event_tag = Gtk_helper.make_tag source ~name:"events" [] in
         Gtk_helper.cleanup_all_tags source;
         let locs_array = LocsArray.create state in
         let index_max =  LocsArray.length locs_array in
         let index = ref 0 in
         while(!index < index_max) do (
           try
             let ((pb,pe),v) = LocsArray.get locs_array !index in
             match v with
             | PStmt (_,ki) ->
               (try
                  let pb,pe = match ki with
                    | {skind = Instr _ | Return _ | Goto _
                               | Break _ | Continue _ | Throw _ } -> pb,pe
                    | {skind = If _ | Loop _
                               | Switch _ } ->
                      (* These statements contain other statements.
                         We highlight only until the start of the first
                         included statement. *)
                      pb,
                      (try LocsArray.find_next locs_array (!index+1)
                             (fun p -> match p with
                                | PStmt _ -> true
                                | _ -> false (* Do not stop on expressions*))
                       with Not_found -> pb+1)
                    | {skind = Block _ | TryExcept _ | TryFinally _
                               | UnspecifiedSequence _ | TryCatch _ } ->
                      pb,
                      (try LocsArray.find_next locs_array (!index+1) (fun _ -> true)
                       with Not_found -> pb+1)
                  in
                  highlighter v ~start:pb ~stop:pe
                with Not_found -> ())
             | PStmtStart _
             | PTermLval _ | PLval _ | PVDecl _ | PGlobal _
             | PIP _ | PExp _ ->
               highlighter v  ~start:pb ~stop:pe
           with Not_found -> () ) ;
           incr index
         done;
         (* React to events on the text *)
         source#apply_tag ~start:source#start_iter ~stop:source#end_iter event_tag;
       in
       Locs.set_hilite state hiliter;
       let gtk_fmt = buffer_formatter state (source:>GText.buffer) in
       let display_global g =
         Printer.with_unfold_precond
           are_preconds_unfolded
           Printer.pp_global gtk_fmt g ;
         Format.pp_print_flush gtk_fmt ()
       in
       let counter = ref 0 in
       begin try
           List.iter
             (fun g ->
                incr counter;
                if !counter > 20 then raise Exit;
                display_global g)
             globals;
         with Exit ->
           Format.fprintf
             gtk_fmt
             "@./* Cannot display more than %d globals at a time. Skipping end \
              of file.@   \
              Use the filetree in 'Flat mode' to navigate the remainder. */@."
             (!counter-1);
           (*let ca = source#create_child_anchor source#end_iter in
             source_view#add_child_at_anchor (GButton.button
             ~text:"See 10 more globals"
             ~callback:(fun _ -> call_cc next_10)
             ()) ca *)
       end;
       source#place_cursor ~where:source#start_iter;
       let last_shown_area =
         Gtk_helper.make_tag source ~name:"last_shown_area"
           [`BACKGROUND "light green"]
       in
       let event_tag = Gtk_helper.make_tag source ~name:"events" [] in
       let id = event_tag#connect#event ~callback:
           (fun ~origin:_ ev it ->
              if !Gtk_helper.gui_unlocked then
                if GdkEvent.get_type ev = `BUTTON_PRESS then begin
                  let coords = GtkText.Iter.get_offset it in
                  try
                    let ((pb,pe), selected) = Locs.find state coords in
                    (* Highlight the pointed term *)
                    source#remove_tag
                      ~start:source#start_iter
                      ~stop:source#end_iter
                      last_shown_area;
                    apply_tag source last_shown_area pb pe;
                    let event_button = GdkEvent.Button.cast ev in
                    let button = GdkEvent.Button.button event_button in
                    host#protect ~cancelable:false
                      (fun () -> selector ~button selected);
                  with Not_found -> () (* no statement at this offset *)
                end;
              false)
       in
       Locs.add_finalizer state
         (fun () -> GtkSignal.disconnect event_tag#as_tag id);
    )

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
