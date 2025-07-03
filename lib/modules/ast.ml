type typ = Bool | Int | Float | String | Path | Named of string | Unit
         | Product of typ list | List of typ | Option of typ

type unary = Not | Neg
type binary = Or | And | Eq | Ne | Lt | Le | Gt | Ge | LShift | RShift
            | Add | Sub | Mul | Div | Mod
            | Concat | Append

(* Patterns are just of the form <enum-name>[::<type>]::<constructor-name>[(<var-names>)] *)
type pattern = string * typ option * string * string list

type expr = Id of string | BoolLit of bool  | IntLit of int | FloatLit of float
          | StringLit of string | PathLit of string | UnitExp
          | GenUnknown of typ
          | ProductExp of expr list
          | RecordExp of expr * (string * expr) list
          | FieldSetExp of expr * string * expr
          | EnumExp   of expr * typ option * string * expr list
          | FuncExp   of expr * expr list
          | ModuleExp of expr * (string * expr) list
          | Field of expr * string
          | ProductField of expr * int
          | UnaryExp of expr * unary
          | BinaryExp of expr * expr * binary
          | CondExp of expr * expr * expr
          | CondProvidedExp of string * expr * expr
          | CondExistsExp of expr * expr * expr
          | ForEachExp of string * expr * stmt list

(* For VarDecls, the bool indicates whether the variables are required or not *)
and  stmt = VarDecls     of bool * (string * string list * typ * expr option) list
          | ForLoop      of string * expr * stmt list
          | IfProvided   of string * stmt list * stmt list
          | IfExists     of expr * stmt list * stmt list
          | IfThenElse   of expr * stmt list * stmt list
          | Match        of expr * (pattern * stmt list) list
          | Clear        of expr
          | Touch        of expr
          | Assert       of expr
          | AssertExists of expr
          | Return       of expr
          | Yield        of expr
          | Assign       of expr * expr
          | LetStmt      of string * expr

type topLevel = Enum      of string * (string * typ list option) list
              | Struct    of string * (string * typ) list
              | Type      of string * typ
              | Uninterp  of string * typ list * typ
              | Attribute of string * typ
              | Element   of string * typ
              | Function  of string * (string * typ) list * typ option * stmt list
              (* Name, aliases, return type, body *)
              | Module    of string list * string list list * typ option * stmt list
