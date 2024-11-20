open Calculus.Ast

exception NotImplemented

(* A 'a list2 is a list with at least two elements *)
type 'a list2 = LastTwo of 'a * 'a | Cons of 'a * 'a list2
type 'a list' = Nil | Singleton of 'a | List of 'a list2

module Ast_Target : Ast_Defs = struct
  type primTy   = Unit | Bool | Int | Float | String | Path | Env

  type field = string
  module FieldMap = Map.Make(String)

  type namedTy = List of typ | Cases of typ list2
  and structTy = Struct of typ FieldMap.t
  and typ = (primTy, namedTy, structTy) typD

  type funct = Proj          of bool * typ * typ (* true = 1, false = 2 *)
             | Constructor   of bool * namedTy   (* true = L, false = R *)
             | EmptyStruct   of structTy
             | AddField      of structTy * field
             | ReadField     of structTy * field
             (* Name and input and output types *)
             | Uninterpreted of string * typ * typ

  type variable = string
  module VariableMap = Map.Make(String)

  type literal = Unit   of unit
               | Bool   of bool
               | Int    of int
               | Float  of float
               | String of string
               | Path   of string
               | Env    of env
   and record = Record of value FieldMap.t
   and value = (primTy, namedTy, structTy, funct, literal, field, record) valueD
   and env = (value * typ) VariableMap.t

  type attribute = string * typ
  type element = string * typ

  type action = Action of string * typ * typ * stmt option ref
  and stmt = (funct, literal, variable, attribute, element, action) stmtD

  type expr = (funct, literal, variable) exprD
  type qual = (funct, literal, variable, attribute, element) qualD
  type attr = (funct, literal, variable, attribute, element) attrD
  type elem = (funct, literal, variable, attribute, element) elemD

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Cases (LastTwo (s, t)) -> (s, t)
    | Cases (Cons (s, ts)) -> (s, Named (Cases ts))
  let structTyDef (Struct fs) = fs

  let funcDef = function
    | Proj (true, s, t)  -> (Product (s, t), s,
                             fun v -> match v with Pair (x, _, _) -> Reduced x
                                      | _ -> Stuck)
    | Proj (false, s, t) -> (Product (s, t), t,
                             fun v -> match v with Pair (_, y, _) -> Reduced y
                                      | _ -> Stuck)
    | Constructor (true, n)  -> (fst (namedTyDef n), Named n,
                                 fun v -> Reduced (Constructor (n, true, v)))
    | Constructor (false, n) -> (snd (namedTyDef n), Named n,
                                 fun v -> Reduced (Constructor (n, false, v)))
    (* Note: We error with structs if they are ever unknown or for any
     * other reason unreducible. For what we're doing structs are really just
     * for arguments and return values to/from modules and so we really want
     * reads to always reduce or error *)
    | EmptyStruct s -> (Primitive Unit, Struct s,
                        fun _ -> Reduced (Struct (s, Record FieldMap.empty)))
    | AddField (s, f) -> (Product (Struct s, FieldMap.find f (structTyDef s)),
                          Struct s,
                          fun v -> match v with Pair (Struct (_, Record fs), x, _)
                                    -> Reduced (Struct (s, Record (FieldMap.add f x fs)))
                                   | _ -> Err "Add field failed to reduce")
    | ReadField (s, f) -> (Struct s, FieldMap.find f (structTyDef s),
                           fun v -> match v with Struct (_, Record fs)
                                    -> begin match FieldMap.find_opt f fs with  
                                       | Some x -> Reduced x
                                       | None -> Err ("Missing field " ^ f)
                                       end
                                    | _ -> Err "Read field failed to reduce")
    (* Uninterpreted functions never reduce *)
    | Uninterpreted (_, in_typ, out_typ) ->
        (in_typ, out_typ, fun _ -> Stuck)

  let literalTyp : literal -> primTy = function
    | Unit   _ -> Unit
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Float  _ -> Float
    | String _ -> String
    | Path   _ -> Path
    | Env    _ -> Env

  let attributeDef (_, typ) : typ = typ

  let elementDef (_, typ) : typ = typ

  let actionDef = function
    | Action (nm, in_typ, out_typ, def) ->
        match !def with
        | Some def -> ("#input", in_typ, out_typ, def)
        | None -> failwith (Printf.sprintf "Function %s was not compiled" nm)

  let isTruthType (t : typ) : bool =
    match t with
    | Primitive Bool -> true
    | _ -> false

  let asTruth (v : value) : bool option =
    match v with
    | Literal (Bool b, Bool) -> Some b
    | _ -> None

  let isUnit (t : typ) : bool =
    match t with
    | Primitive Unit -> true
    | _ -> false

  let envType : typ = Primitive Env
  let envToVal (env : env) = Literal (Env env, (Env : primTy))
  let envFromVal (v : value) =
    match v with Literal (Env env, _) -> env | _ -> failwith "Not environment"
end
