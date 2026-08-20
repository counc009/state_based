open Builtin

module type AST = sig
  type lit
  type func
  type act

  type att = string
  type elm = string

  type expr = Function of func * expr
            | Literal  of lit
            | Variable of string
            | Pair     of expr * expr
            | Element  of expr * elm * expr

  (* A value representing the state reference *)
  type base = expr
  type qual = QualAttr of base * att * expr
            | QualPosE of base * elm * expr
            | QualNegE of base * elm * expr
  type attr = base * att
  type elem = base * elm * expr

  type stmt = Seq        of stmt * stmt
            | Action     of string * act * expr
            | Assign     of string * expr
            | Add        of qual
            | Get        of string * attr
            | Contains   of elem * stmt * stmt
            | Cond       of expr * stmt * stmt
            (* The string is the name of the value within the constructor *)
            | Match      of expr * string * stmt * stmt
            (* First string is the result's name and second is the loop var *)
            | ForEach    of string * expr * string * stmt
            | While      of expr * stmt
            (* Loop over each element on a state of a particular element label.
             * The loop variable stores the argument of the element in each
             * iteration. The order of iteration is unspecified. *)
            | ForElem    of base * elm * string * stmt
            | TryCatch   of stmt * string * stmt
            | TryFinally of stmt * stmt
            | Localize   of elm * expr * stmt
            | Raise      of expr
            | Return     of expr
            | Yield      of expr
            | Pass
end

module Ast (B : BUILTIN) : AST with type lit  = B.lit
                                and type func = B.func
                                and type act  = B.act
= struct
  type lit  = B.lit
  type func = B.func
  type act  = B.act

  type att = string
  type elm = string

  type expr = Function of func * expr
            | Literal  of lit
            | Variable of string
            | Pair     of expr * expr
            | Element  of expr * elm * expr

  (* A value representing the state reference *)
  type base = expr
  type qual = QualAttr of base * att * expr
            | QualPosE of base * elm * expr
            | QualNegE of base * elm * expr
  type attr = base * att
  type elem = base * elm * expr

  type stmt = Seq        of stmt * stmt
            | Action     of string * act * expr
            | Assign     of string * expr
            | Add        of qual
            | Get        of string * attr
            | Contains   of elem * stmt * stmt
            | Cond       of expr * stmt * stmt
            (* The string is the name of the value within the constructor *)
            | Match      of expr * string * stmt * stmt
            (* First string is the result's name and second is the loop var *)
            | ForEach    of string * expr * string * stmt
            | While      of expr * stmt
            (* Loop over each element on a state of a particular element label.
             * The loop variable stores the argument of the element in each
             * iteration. The order of iteration is unspecified. *)
            | ForElem    of base * elm * string * stmt
            | TryCatch   of stmt * string * stmt
            | TryFinally of stmt * stmt
            | Localize   of elm * expr * stmt
            | Raise      of expr
            | Return     of expr
            | Yield      of expr
            | Pass
end
