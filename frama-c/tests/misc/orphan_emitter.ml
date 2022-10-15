module P =
  Plugin.Register
    (struct
      let name = "Orphan"
      let shortname = "orphan"
      let help = ""
     end)

module S =
  P.True(struct let option_name = "-orphan" let help = "" end)

let emitter1 =
  Emitter.create "emitter1" [ Emitter.Code_annot ]
    ~correctness:[ S.parameter ] ~tuning:[]

let main () =
  let kf = Globals.Functions.find_by_name "main" in
  let stmt = Kernel_function.find_first_stmt kf in
  Annotations.add_assert emitter1 stmt Logic_const.ptrue

let () = Db.Main.extend main
