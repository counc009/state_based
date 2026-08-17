module type AST = sig
  type lit
  type func
  type act

  type expr = Function of func * expr
            | Literal  of lit
            | Variable of string
            | Pair     of expr * expr

  type att = string
  type elm = string

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
            (* Contains now returns a reference to the nested state on the
             * element in the then branch *)
            | Contains   of elem * string * stmt * stmt
            | Cond       of expr * stmt * stmt
            (* The string is the name of the value within the constructor *)
            | Match      of expr * string * stmt * stmt
            (* First string is the result's name and second is the loop var *)
            | ForEach    of string * expr * string * stmt
            | While      of expr * stmt
            | TryCatch   of stmt * string * stmt
            | TryFinally of stmt * stmt
            | Localize   of elm * expr * stmt
            | Raise      of expr
            | Return     of expr
            | Yield      of expr
            | Pass
end

module type LITERALS = sig
  type t
end
module type FUNCTIONS = sig
  type t
end
module type ACTIONS = sig
  type t
end

module Ast(L : LITERALS)(F : FUNCTIONS)(A : ACTIONS)
  : AST with type lit = L.t
        with type func = F.t
        with type act = A.t
= struct
  type lit  = L.t
  type func = F.t
  type act  = A.t

  type expr = Function of func * expr
            | Literal  of lit
            | Variable of string
            | Pair     of expr * expr

  type att = string
  type elm = string

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
            (* Contains now returns a reference to the nested state on the
             * element in the then branch *)
            | Contains   of elem * string * stmt * stmt
            | Cond       of expr * stmt * stmt
            (* The string is the name of the value within the constructor *)
            | Match      of expr * string * stmt * stmt
            (* First string is the result's name and second is the loop var *)
            | ForEach    of string * expr * string * stmt
            | While      of expr * stmt
            | TryCatch   of stmt * string * stmt
            | TryFinally of stmt * stmt
            | Localize   of elm * expr * stmt
            | Raise      of expr
            | Return     of expr
            | Yield      of expr
            | Pass
end
