open Ast

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
end

(* Construct a VALUE module from an AST instance *)
module Value(C : AST) : VALUE with type lit = C.lit = struct
  type lit = C.lit
  module FieldMap = Map.Make(String)

  type t = Literal of lit
         | Pair    of t * t
         | Left    of t
         | Right   of t
         | Struct  of t FieldMap.t
         | SRef    of s
  and  s = Here
         | Nested of string * t * s
end
