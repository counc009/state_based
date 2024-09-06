open Ast

module rec Ast_Base_Types : Ast_Types = struct
  open Ast_Base

  type namedTy  = List of typ | Either of typ * typ
  and  structTy = (string * typ) list
  and  primTy   = Unit | Bool | Int | Float | String | Path

  type field = string
  module FieldMap = Map.Make(String)

  type attribute = Content | Files | Dirs | User | Group
  type element = File | Directory

  type action = Copy
  type funct = LineInFile | Download | Template | GitClone
  type literal = Unit   of unit
               | Bool   of bool
               | Int    of int
               | Float  of float
               | String of string
               | Path   of string

  type variable = string
  module VariableMap = Map.Make(String)
end
and Ast_Base : AST = Ast(Ast_Base_Types)

module Ast_Base_Defs : Ast_Defs = struct
  module Types = Ast_Base_Types
  module Ast = Ast_Base

  let namedTyDef : Ast_Base_Types.namedTy -> Ast.typ * Ast.typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Either (s, t) -> (s, t)
  let structTyDef fs = FieldMap.of_seq (List.to_seq fs)
  let attributeDef = function
    | Content -> Primitive String
    | Files   -> Named (List (Primitive Path))
    | Dirs    -> Named (List (Primitive Path))
    | User    -> Primitive String
    | Group   -> Primitive String
  let elementDef = function
    | File      -> Primitive Path
    | Directory -> Primitive Path
  let literalTyp : literal -> primTy = function
    | Unit   _ -> Unit
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Float  _ -> Float
    | String _ -> String
    | Path   _ -> Path

  exception NotImplemented
  let actionDef = function
    | Copy -> raise NotImplemented
end
