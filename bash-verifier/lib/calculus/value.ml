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
end
