class a =
  let x = 1 in
object(self)
  method get_x_a = x
  val y = 2
  method get_y_a = y
  val z = 3
  method private t = 4
  method get_t_a = self#t
end

class b =
object(self)
  inherit a as super
  (* method get_x_b = x (* ill-typed: no x in env *) *)
  val y = 4
  method get_y_b = y
  method get_z_b = z
  method t = 5
  method get_t_b = super#t
end

let bobj = new b;;

Printf.printf "get_x_a:%d\nget_y_a:%d\nget_y_b:%d\nget_z_b:%d\nget_t_a:%d\nget_t_b:%d\n" bobj#get_x_a bobj#get_y_a bobj#get_y_b bobj#get_z_b bobj#get_t_a
bobj#get_t_b
