let depend_files = ref []

let add_deps s = depend_files:= s :: !depend_files

let root = ref ""

module Dep_graph = Graph.Imperative.Digraph.Concrete(
  struct
    type t = string
    let compare = String.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)

module Dfs = Graph.Traverse.Dfs(Dep_graph)

module Topological = Graph.Topological.Make(Dep_graph)

module String_set = Set.Make(String)

let dependencies = Dep_graph.create ()

let tokenize_input chan =
  let rec aux acc =
    let line = input_line chan in
    let tokens = Str.(split (regexp " +") line) in
    match List.rev tokens with
    | "\\" :: tail -> aux (tail @ acc)
    | l -> l @ acc
  in
  List.rev (aux [])

let add_edge user provider =
  if Filename.check_suffix user ".cmx" &&
     Filename.check_suffix provider ".cmx"
  then Dep_graph.add_edge dependencies user provider

let parse_one_dependency chan =
  match tokenize_input chan with
  | [] -> () (* Empty line *)
  | target :: ":" :: deps ->
    List.iter (add_edge target) deps;
  | _ -> failwith ("ill formed rule")

let read_dep_file file =
  let chan = open_in file in
  try
    while true do
      parse_one_dependency chan
    done;
  with End_of_file -> close_in chan

let usage =
  Printf.sprintf
    "usage: %s -root file.cmx -deps .depend\n\
     provides the ordered list of .cmx needed to link file.cmx \
     (excluding the latter)"
    (Filename.basename Sys.executable_name)

let err_usage () = Printf.printf "%s\n%!" usage; exit 2

let arguments =
  [ "-deps", Arg.String add_deps, "add a .depend file to set of dependencies";
    "-root", Arg.Set_string root, "root of the dependencies computation";
  ]

let () =
  Arg.parse arguments (fun _ -> err_usage()) usage;
  List.iter read_dep_file !depend_files;
  let add v acc = if v = !root then acc else String_set.add v acc in
  let res = Dfs.fold_component add String_set.empty dependencies !root in
  let l =
    Topological.fold
      (fun s acc -> if String_set.mem s res then s :: acc else acc)
      dependencies []
  in
  Format.(printf "@[<h>%a@]"
            (pp_print_list
               ~pp_sep:(fun fmt () -> pp_print_string fmt " ") pp_print_string)
            l)
