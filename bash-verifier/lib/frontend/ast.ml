open Stdint

type typ = Void | Bool
         | SInt8 | UInt8 | SInt16 | UInt16 | SInt32 | UInt32 | SInt64 | UInt64
         | Float32 | Float64
         | Function of typ * typ list (* return type and argument types *)
         (* Types that are mostly internal and not related to C *)
         | StateRef | String
         | Product of typ list | Struct of (string * typ) list
         | Named of string * typ list

type unary = Neg | LNot | BNot

type binary = Mul | Div | Mod | Add | Sub | LShft | RShft
            | Lt | Le | Gt | Ge | Eq | Ne
            | BAnd | LAnd | BXor | BOr | LOr

type pattern = { enum: string; constr: string; vars: string list }

type expr = Id        of string
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
          | CastExp   of expr * typ
          | TupleExp  of expr list
          | StructExp of string * typ list * (string * expr) list
          | EnumExp   of string * typ list * string * expr list
          | FuncExp   of expr * typ list * expr list
          | CondExp   of expr * expr * expr
          | Exists    of expr
          | ForEach   of string * expr * stmt list

and stmt = ForLoop    of string * expr * stmt list
         | IfThenElse of expr * stmt list * stmt list
         (* Contains a default pattern in case no other pattern matched *)
         | Match      of expr * (pattern * stmt list) list * stmt list
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
         | LetStmt    of string * typ option * expr
         | Localize   of stmt list

type decl = Enum      of { name: string; ty_args: string list;
                            constrs: (string * typ list) list }
          | Struct    of { name: string; ty_args: string list;
                            fields: (string * typ) list }
          | Type      of { name: string; def: typ }
          | Uninterp  of { name: string; ty_args: string list;
                            args: typ list; ret: typ }
          | Attribute of { local: bool; name: string; ty: typ }
          | Element   of { local: bool; name: string; ty: typ list }
          | Exception of { name: string; ty: typ list }
          | Function  of { name: string; ty_args: string list;
                            args: (string * typ) list; ret: typ;
                            body: stmt list }
