type typ = Void | Bool
         | SInt8 | UInt8 | SInt16 | UInt16 | SInt32 | UInt32 | SInt64 | UInt64
         | Float32 | Float64
         | Pointer of typ | Array of typ * int
         | Struct of (string * typ) list | Union of (string * typ) list
         | Function of typ * typ list (* return type and argument types *)
         (* Types that are mostly internal and not related to C *)
         | StateRef | Product of typ list
         | Named of string * typ list option

type unary = Neg | LNot | BNot

type binary = Mul | Div | Mod | Add | Sub | LShft | RShft
            | Lt | Le | Gt | Ge | Eq | Ne
            | BAnd | LAnd | BXor | BOr | LOr

type pattern =
  { enum: string; ty: typ option; constr: string; vars: string list }

type expr = Id        of string
          | BoolLit   of bool
          | IntLit    of string (* to ensure we preserve it properly *)
          | FloatLit  of string
          | StringLit of string
          | CharLit   of char
          | UnitLit
          | UnaryExp  of unary * expr
          | BinaryExp of expr * binary * expr
          | TupleExp  of expr list
          | FieldExp  of expr * string
          | ProdField of expr * int
          | EnumExp   of string * typ option * string * expr list
          | FuncExp   of expr * typ option * expr list
          | CondExp   of expr * expr * expr
          | Exists    of expr
          | ForEach   of string * expr * stmt list
          | SizeOf    of typ

and stmt = ForLoop    of string * expr * stmt list
         | IfThenElse of expr * stmt list * stmt list
         | Match      of expr * (pattern * stmt list) list
         | TryCatch   of stmt list
                       * (string * string list * stmt list) option (* catch *)
                       * stmt list (* finally *)
         | Clear      of expr
         | Touch      of expr
         | Assert     of expr
         | Return     of expr
         | Yield      of expr
         | Raise      of string * expr (* Exception name and argument *)
         | Assign     of expr * expr
         | LetStmt    of string * expr
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
