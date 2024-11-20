type typ = Bool | Int | Float | String | Path | Named of string | Unit
         | Product of typ list | List of typ

type unary = Not | Neg
type binary = Or | And | Eq | Ne | Lt | Le | Gt | Ge | LShift | RShift
            | Add | Sub | Mul | Div | Mod

type expr = Id of string | BoolLit of bool  | IntLit of int | FloatLit of float
          | StringLit of string | UnitExp   | ProductExp of expr list
          | RecordExp of expr * (string * expr) list
          | FuncExp   of expr * expr list
          | ModuleExp of expr * (string * expr) list
          | Field of expr * string
          | ProductField of expr * int
          | UnaryExp of expr * unary
          | BinaryExp of expr * expr * binary

(* Patterns are just of the form <name>[(<names>)] *)
type pattern = string * string list

type stmt = RequiredVar of (string * string list * typ * expr option) list
          | OptionalVar of (string * string list * typ * expr option) list
          | ForLoop     of string * expr * stmt list
          | IfProvided  of string * stmt list * stmt list
          | IfThenElse  of expr * stmt list * stmt list
          | Match       of expr * (pattern * stmt list) list
          | Clear       of expr
          | Assert      of expr
          | Return      of expr
          | Assign      of expr * expr

type topLevel = Enum      of string * (string * typ option) list
              | Struct    of string * (string * typ) list
              | Uninterp  of string * typ * typ
              | Attribute of string * typ
              | Element   of string * typ
              | Function  of string * (string * typ) list * typ option * stmt list
              | Module    of string list * typ option * stmt list

