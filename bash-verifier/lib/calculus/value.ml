open Builtin

module type VALUE = sig
  type lit
  module FieldMap : Map.S with type key = string

  type t = Literal of lit
         | Pair    of t * t
         | Left    of t
         | Right   of t
         | Struct  of t FieldMap.t
         | SRef    of s
  and  s = Here
         | Nested of string * t * s

  val string_of_value : t -> string
end

module Value (B : BUILTIN) : VALUE with type lit = B.lit = struct
  type lit = B.lit
  module FieldMap = Map.Make(String)

  type t = Literal of lit
         | Pair    of t * t
         | Left    of t
         | Right   of t
         | Struct  of t FieldMap.t
         | SRef    of s
  and  s = Here
         | Nested of string * t * s

  let rec string_of_value = function
    | Literal l -> B.string_of_lit l
    | Pair (x, y) ->
        Printf.sprintf "(%s, %s)" (string_of_value x) (string_of_value y)
    | Left x  -> Printf.sprintf "L(%s)" (string_of_value x)
    | Right x -> Printf.sprintf "R(%s)" (string_of_value x)
    | Struct xs ->
        let string_of_bind nm v = nm ^ " = " ^ string_of_value v
        in let fields =
          FieldMap.fold (fun nm v res -> string_of_bind nm v :: res) xs []
        in Printf.sprintf "{ %s }" (String.concat ", " fields)
    | SRef s ->
        let rec string_of_s = function
          | Here -> "\x08"
          | Nested (elem, v, n) ->
              Printf.sprintf "%s(%s).%s" elem (string_of_value v) (string_of_s n)
        in string_of_s s
end
