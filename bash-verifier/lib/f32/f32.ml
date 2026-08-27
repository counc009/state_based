type t = int32

external add : t -> t -> t = "f32_add"
external sub : t -> t -> t = "f32_sub"
external mul : t -> t -> t = "f32_mul"
external div : t -> t -> t = "f32_div"

external abs : t -> t = "f32_abs"
external neg : t -> t = "f32_neg"

external of_float : float -> t = "f32_of_double"
external to_float : t -> float = "f32_to_double"

let compare : t -> t -> int = Stdlib.compare

let zero = of_float 0.0
let one  = of_float 1.0

let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div

let of_string s = of_float (Float.of_string s)
let of_string_opt s = Option.map of_float (Float.of_string_opt s)
let to_string f = Float.to_string (to_float f)
let printer c f = Printf.fprintf c "%f" (to_float f)
