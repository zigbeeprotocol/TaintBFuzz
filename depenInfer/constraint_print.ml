open Cil_types

let help_msg = "Print out condition constraint variables"
module Self = Plugin.Register
  (struct
	let name = "constraint variables"
	let shortname = "constrVar"
	let help = help_msg
  end)

module Enabled = Self.False
  (struct
    let option_name = "-constr-vars"
	let help = "when on (off by default), computes the constraint variables of all functions."
  end)
  
module OutputFile = Self.String
  (struct
    let option_name = "-constr-vars-output"
	let default = "constrVar.json"
	let arg_name = "output-file"
	let help = "file where the constraint variables are output, in json format"
  end)

let rec print_expression out exp = 
  match exp.enode with
  | Const const -> Format.fprintf out "\"%a\"" Printer.pp_constant const
  | Lval lv | AddrOf lv | StartOf lv ->  
	Format.fprintf out "\"%a\"" Printer.pp_lval lv
  | SizeOf v | AlignOf v -> Format.fprintf out "\"%a\"" Printer.pp_typ v
  | SizeOfE e | AlignOfE e | UnOp (_,e,_) | CastE (_,e) -> 
	print_expression out e
  | SizeOfStr s -> Format.pp_print_string out s
  | BinOp(_,e1,e2,_) ->
	print_expression out e1;
	match e2.enode with
	| Const _ -> ()
	| _ -> Format.fprintf out ",%a" print_expression e2

let rec print_stmt out s = 
  match s.skind with
  | Instr (Call (_,e1,e2,_)) -> 
      Format.fprintf out "{\"stmt\":\"%a\"," Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s);
	  Format.fprintf out "\"type\":\"call\",\"func\":%a,\"vars\":[%a]}stmt_end\n" 
	  print_expression e1
	  (Pretty_utils.pp_iter ~sep:","
	    List.iter print_expression) e2
  | Goto (sref,_) ->
      Format.fprintf out "{\"stmt\":\"%a\"," Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s);
      Format.fprintf out "\"type\":\"goto\",\"target\":\"%a\"}stmt_end\n" Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc !sref);
  | Continue loc -> 
	  Format.fprintf out "{\"stmt\":\"%a\"," Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s);
      Format.fprintf out "\"type\":\"continue\",\"target\":\"%a\"}stmt_end\n" Cil_datatype.Location.pretty_line loc;
  | If (e,_,_,_) -> 
      Format.fprintf out "{\"stmt\":\"%a\"," Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s);
      Format.fprintf out "\"type\":\"if\",\"vars\":[%a]}stmt_end\n" print_expression e
  | Switch(e,_,_,_) -> 
	  Format.fprintf out "{\"stmt\":\"%a\"," Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s);
      Format.fprintf out "\"type\":\"switch\",\"vars\":[%a]}stmt_end\n" print_expression e
  | Loop _ -> 
	  Format.fprintf out "{\"stmt\":\"%a\",\"type\":\"loop\",\"vars\":[%a]}stmt_end\n" 
	  Cil_datatype.Location.pretty_line (Cil_datatype.Stmt.loc s)
	  (Pretty_utils.pp_iter ~sep:","
	    List.iter print_stmt) s.succs
  | _ -> ()
  
class print_conditions out = object
  inherit Visitor .frama_c_inplace
  method! vfile _ =
	Format.fprintf out "[";
	Cil.DoChildrenPost (fun f -> Format.fprintf out "]"; f)
	
  method! vglob_aux g =
	match g with
	| GFun(f,_) ->
		Format.fprintf out "{\"function\":\"%a\",\"constraints\":[" Printer.pp_varinfo f.svar;
		Cil.DoChildrenPost(fun g -> Format.fprintf out "]}func_end\n"; g)
	| _ -> Cil.SkipChildren
	
  method! vstmt_aux s =
    Format.fprintf out "%a" print_stmt s;	
	Cil.DoChildren
end

let run () =
  if Enabled.get() then
    let filename = OutputFile.get () in
    let chan = open_out filename in
    let fmt = Format.formatter_of_out_channel chan in
    Visitor.visitFramacFileSameGlobals (new print_conditions fmt) (Ast.get ());
    close_out chan

let () = Db.Main.extend run