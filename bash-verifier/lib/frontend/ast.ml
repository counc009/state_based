open Stdint

module type ANNOTATOR = sig
  type 'a declannt
  type 'a exprannt
  type 'a stmtannt
  type 'a elemannt (* The type of an element, where 'a is the expr type *)
  type 'a idannt   (* Annotation for an identifier *)
  type 'a litannt  (* Annotation for a literal value *)

  type 's cases
  type typ
end

module Ast(A : ANNOTATOR) = struct
  type unary = Neg | LNot | BNot

  type binary = Mul | Div | Mod | Add | Sub | LShft | RShft
              | Lt | Le | Gt | Ge | Eq | Ne
              | BAnd | LAnd | BXor | BOr | LOr

  type id = string A.idannt

  type expr_base =
    | Id        of id
    | BoolLit   of bool A.litannt
    | Int8Lit   of int8 A.litannt
    | Int16Lit  of int16 A.litannt
    | Int32Lit  of int32 A.litannt
    | Int64Lit  of int64 A.litannt
    | UInt8Lit  of uint8 A.litannt
    | UInt16Lit of uint16 A.litannt
    | UInt32Lit of uint32 A.litannt
    | UInt64Lit of uint64 A.litannt
    | F32Lit    of F32.t A.litannt
    | F64Lit    of float A.litannt
    | StringLit of string A.litannt
    | CharLit   of char A.litannt
    | UnitLit   of unit A.litannt
    | UnaryExp  of unary * expr
    | BinaryExp of expr * binary * expr
    | FieldExp  of expr * id
    | ProdField of expr * int A.litannt
    | CastExp   of expr * A.typ
    | TupleExp  of expr list
    | StructExp of id * A.typ list * (id * expr) list
    | EnumExp   of id * A.typ list * id * expr list
    | FuncExp   of expr * A.typ list * expr list
    | CondExp   of expr * expr * expr
    | Exists    of elem
    | ForEach   of id * expr * stmt list
    | ForAll    of elem option * id * id list * stmt list
    (* Not used in parsing but useful after semantic analysis to separate
     * struct accesses and state accesses *)
    | Element   of elem
    | Attribute of elem * id
  and expr = expr_base A.exprannt
  and elem = expr_base A.elemannt

  and stmt_base =
    | ForLoop    of id * expr * stmt list
    | ForElem    of elem option * id * id list * stmt list
    | WhileLoop  of expr * stmt list
    | IfThenElse of expr * stmt list * stmt list
    | Match      of expr * (stmt list) A.cases
    | TryCatch   of stmt list
                  * (id * id list * stmt list) option (* catch *)
                  * stmt list (* finally *)
    | Clear      of elem
    | Touch      of elem
    | Assert     of expr
    | Return     of expr
    | Yield      of expr
    | Raise      of id * expr list (* Exception name and arguments *)
    | Assign     of expr * expr
    | LetStmt    of id * A.typ option * expr
    | Localize   of stmt list
  and stmt = stmt_base A.stmtannt

  type decl_base = 
    | Enum      of { name: id; ty_args: id list;
                      constrs: (id * A.typ list) list }
    | Struct    of { name: id; ty_args: id list;
                      fields: (id * A.typ) list }
    | Type      of { name: id; def: A.typ }
    | Uninterp  of { name: id; ty_args: id list;
                      args: A.typ list; ret: A.typ }
    | Attribute of { local: bool; name: id; ty: A.typ }
    | Element   of { local: bool; name: id; ty: A.typ list }
    | Exception of { name: id; ty: A.typ list }
    | Function  of { name: id; ty_args: id list;
                      args: (id * A.typ) list; ret: A.typ;
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
    type 'a elemannt = 'a annt

    type 'a idannt   = 'a
    type 'a litannt  = 'a

    type 's cases = (pattern * 's) list * 's
    type typ = typ_annt
  end)
end
