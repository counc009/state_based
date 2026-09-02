open Stdint

module type ANNOTATOR = sig
  type 'a declannt
  type 'a exprannt
  type 'a stmtannt

  type 's cases
  type typ
end

module Ast(A : ANNOTATOR) = struct
  type unary = Neg | LNot | BNot

  type binary = Mul | Div | Mod | Add | Sub | LShft | RShft
              | Lt | Le | Gt | Ge | Eq | Ne
              | BAnd | LAnd | BXor | BOr | LOr

  type expr_base =
    | Id        of string
    | BoolLit   of bool
    | Int8Lit   of int8
    | Int16Lit  of int16
    | Int32Lit  of int32
    | Int64Lit  of int64
    | UInt8Lit  of uint8
    | UInt16Lit of uint16
    | UInt32Lit of uint32
    | UInt64Lit of uint64
    | F32Lit    of F32.t
    | F64Lit    of float
    | StringLit of string
    | CharLit   of char
    | UnitLit
    | UnaryExp  of unary * expr
    | BinaryExp of expr * binary * expr
    | FieldExp  of expr * string
    | ProdField of expr * int
    | CastExp   of expr * A.typ
    | TupleExp  of expr list
    | StructExp of string * A.typ list * (string * expr) list
    | EnumExp   of string * A.typ list * string * expr list
    | FuncExp   of expr * A.typ list * expr list
    | CondExp   of expr * expr * expr
    | Exists    of expr
    | ForEach   of string * expr * stmt list
  and expr = expr_base A.exprannt

  and stmt_base =
    | ForLoop    of string * expr * stmt list
    | WhileLoop  of expr * stmt list
    | IfThenElse of expr * stmt list * stmt list
    | Match      of expr * (stmt list) A.cases
    | TryCatch   of stmt list
                  * (string * string list * stmt list) option (* catch *)
                  * stmt list (* finally *)
    | Clear      of expr
    | Touch      of expr
    | Assert     of expr
    | Return     of expr
    | Yield      of expr
    | Raise      of string * expr list (* Exception name and arguments *)
    | Assign     of expr * expr
    | LetStmt    of string * A.typ option * expr
    | Localize   of stmt list
  and stmt = stmt_base A.stmtannt

  type decl_base = 
    | Enum      of { name: string; ty_args: string list;
                      constrs: (string * A.typ list) list }
    | Struct    of { name: string; ty_args: string list;
                      fields: (string * A.typ) list }
    | Type      of { name: string; def: A.typ }
    | Uninterp  of { name: string; ty_args: string list;
                      args: A.typ list; ret: A.typ }
    | Attribute of { local: bool; name: string; ty: A.typ }
    | Element   of { local: bool; name: string; ty: A.typ list }
    | Exception of { name: string; ty: A.typ list }
    | Function  of { name: string; ty_args: string list;
                      args: (string * A.typ) list; ret: A.typ;
                      body: stmt list }
  and decl = decl_base A.declannt
end

module Parsed = struct
  type 'a annt = { ast : 'a; pos : Lexing.position * Lexing.position }

  type typ_base =
    | Void | Bool
    | SInt8 | UInt8 | SInt16 | UInt16 | SInt32 | UInt32 | SInt64 | UInt64
    | Float32 | Float64
    | Function of typ_annt * typ_annt list (* return type and argument types *)
    (* Types that are mostly internal and not related to C *)
    | StateRef | String
    | Product of typ_annt list | Named of string * typ_annt list
    | List of typ_annt
  and typ_annt = typ_base annt

  type typ = typ_annt

  type pattern_base = { enum: string; constr: string; vars: string list }
  and pattern = pattern_base annt

  type 's cases = (pattern * 's) list * 's

  include Ast(struct
    type 'a declannt = 'a annt
    type 'a exprannt = 'a annt
    type 'a stmtannt = 'a annt

    type 's cases = (pattern * 's) list * 's
    type typ = typ_annt
  end)
end
