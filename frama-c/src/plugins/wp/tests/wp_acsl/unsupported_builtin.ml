open Cil_types

let builtin = {
  bl_name = "unimplemented_builtin" ;
  bl_labels = [] ;
  bl_params = [] ;
  bl_type = None ;
  bl_profile = [] ;
}

let () =
  Logic_builtin.add builtin
