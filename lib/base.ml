open Ast

exception NotImplemented

module Ast_Base : Ast_Defs = struct
  type primTy   = Unit | Bool | Int | Float | String | Path

  type namedTy  = List of typ | Either of typ * typ
  and  structTy = Struct of (string * typ) list
  and typ = (primTy, namedTy, structTy) typD

  type field = string
  module FieldMap = Map.Make(String)

  type funct = Proj        of bool * typ * typ (* true = 1, false = 2 *)
             | Constructor of bool * namedTy   (* true = L, false = R *)
             | EmptyStruct of structTy
             | AddField    of structTy * field
             | ReadField   of structTy * field
             | RemoveField of structTy * field
             | LineInString | Download | Template | GitClone

  type literal = Unit   of unit
               | Bool   of bool
               | Int    of int
               | Float  of float
               | String of string
               | Path   of string

  type variable = string
  module VariableMap = Map.Make(String)

  type attribute = Content | Files | Dirs | User | Group
  type element = File | Directory

  type action = Copy

  type expr = (funct, literal, variable) exprD
  type value = (primTy, namedTy, structTy, funct, literal, field) valueD
  type qual = (funct, literal, variable, attribute, element) qualD
  type bqual = (funct, literal, variable, attribute, element) bqualD
  type attr = (funct, literal, variable, attribute, element) attrD
  type stmt = (funct, literal, variable, attribute, element, action) stmtD

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Either (s, t) -> (s, t)
  let structTyDef (Struct fs) = FieldMap.of_seq (List.to_seq fs)

  let funcDef = function
    | Proj (true, s, t)  -> (Product (s, t), s, fun _ -> None)
    | Proj (false, s, t) -> (Product (s, t), t, fun _ -> None)
    | Constructor (true, n)  -> (fst (namedTyDef n), Named n, fun _ -> None)
    | Constructor (false, n) -> (snd (namedTyDef n), Named n, fun _ -> None)
    | EmptyStruct s -> (Primitive Unit, Struct s, fun _ -> None)
    | AddField (s, f) -> (Product (Struct s, FieldMap.find f (structTyDef s)),
                          Struct s,
                          fun _ -> None)
    | ReadField (s, f) -> (Struct s, FieldMap.find f (structTyDef s), fun _ -> None)
    | RemoveField (s, _) -> (Struct s, Struct s, fun _ -> None)
    | LineInString -> (Product (Primitive String, Primitive String),
                       Primitive String,
                       fun _ -> None)
    | Download -> (Primitive String, (* Path? URL? *)
                   Primitive String,
                   fun _ -> None)
    | Template -> (Primitive String, Primitive String, fun _ -> None)
    | GitClone -> (Primitive String, (* Path? URL? *)
                   Primitive String,
                   fun _ -> None)

  let literalTyp : literal -> primTy = function
    | Unit   _ -> Unit
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Float  _ -> Float
    | String _ -> String
    | Path   _ -> Path

  let attributeDef : attribute -> typ = function
    | Content -> Primitive String
    | Files   -> Named (List (Primitive Path))
    | Dirs    -> Named (List (Primitive Path))
    | User    -> Primitive String
    | Group   -> Primitive String

  let elementDef : element -> typ = function
    | File      -> Primitive Path
    | Directory -> Primitive Path

  let actionDef = function
    | Copy -> raise NotImplemented
end
