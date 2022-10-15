(* Point de programme *)
type t_program_point ;;

(* Instruction *)
type t_stmt ;;

(* l'instruction située à un point de contrôle (après) *)
val get_pp_stmt : t_program_point -> t_stmt ;;

(* CFG : control flow graph *)
type t_cfg ;;
(* successeurs dans le cfg. *)
val get_cfg_succ : t_cfg -> t_stmt -> t_stmt list ;;
(* predecesseurs dans le cfg. *)
val get_cfg_prev : t_cfg -> t_stmt -> t_stmt list ;;

(* PDG : program dependences graph *)
type t_pdg ;;
(* element composant le PDG *)
type t_elem ;;
(* donne la liste des dépendances directes de l'élément dans le PDG *)
val get_dpds : t_elem -> t_pdg -> t_elem list ;;
val get_all_dpds : t_pdg -> t_elem -> t_elem list ;;
val get_list_all_dpds : t_pdg -> t_elem list -> t_elem list ;;
val get_list_control_dpds : t_pdg -> t_elem list -> t_elem list ;;
val get_list_all_control_dpds : t_pdg -> t_elem list -> t_elem list ;;
val merge :  t_elem list -> t_elem list -> t_elem list ;;

val get_pp_elems : t_pdg -> t_program_point -> t_elem list ;;

(* correspondance entre les instructions et les éléments du PDG *)
type t_stmt_elems ;;

(* retrouver l'instruction correspondant à un élément *)
val get_stmt : t_elem -> t_stmt_elems -> t_stmt ;;
(* retrouver les instructions correspondant aux éléments *)
val get_stmts : t_elem list -> t_stmt_elems -> t_stmt list ;;
(* retrouver les éléments correspondant à une instruction *)
val get_elems : t_stmt -> t_stmt_elems -> t_elem list ;;

type t_state 

type t_data

val get_state : t_program_point -> t_state ;;
val get_defs_data : t_state -> t_data ->  t_elem list ;;
(* type des marques *)
type t_mark ;;
(* la marque correspondant à mS : superflu. *)
val spare_mark : t_mark ;;
(* combinaison de deux marques *)
val combine_mark : t_mark -> t_mark -> t_mark ;;

(* type correspondant au marquage des instructions d'une fonction. *)
type t_ff ;;
(* lire la marque associée à une instruction dans le marquage *)
val get_stmt_mark : t_stmt -> t_ff -> t_mark ;;
(* remplacer la marque associée à une instruction dans le marquage *)
val replace_stmt_mark : t_ff -> t_stmt -> t_mark -> t_ff ;;
