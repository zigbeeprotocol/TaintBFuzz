module Value_is_computed = State_builder.Ref
  (Datatype.Bool)
  (struct
    let name = "Data_for_cfg.Value_computed"
    let dependencies = []
    let default () = false
   end);;
