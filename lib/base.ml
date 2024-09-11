open Ast

exception NotImplemented

module Ast_Base : Ast_Defs = struct
  type primTy   = Unit | Bool | Int | Float | String | Path | Env

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


  type attribute = Content | Files | Dirs | User | Group
  type element = File | Directory

  type action = Copy

  type expr = (funct, literal, variable) exprD
  type qual = (funct, literal, variable, attribute, element) qualD
  type bqual = (funct, literal, variable, attribute, element) bqualD
  type attr = (funct, literal, variable, attribute, element) attrD
  type stmt = (funct, literal, variable, attribute, element, action) stmtD

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Either (s, t) -> (s, t)
  let structTyDef (Struct fs) = FieldMap.of_seq (List.to_seq fs)

  (* FIXME: Don't use Str maybe? *)
  let is_substring sub str =
    let re = Str.regexp_string sub
    in try ignore (Str.search_forward re str 0); true
       with Not_found -> false

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
    | RemoveField (s, f) -> (Struct s, Struct s,
                             fun v -> match v with Struct (_, Record fs)
                                      -> Reduced (Struct (s, Record (FieldMap.remove f fs)))
                                      | _ -> Err "Removed field failed to reduce")
    (* First is string, second is desired line (no end line) *)
    | LineInString -> (Product (Primitive String, Primitive String),
                       Primitive String,
                       fun v -> match v with Pair (Literal (String s, _), Literal (String l, _), _)
                                  -> if is_substring l (s ^ "\n")
                                     then Reduced (Literal (String s, String))
                                     else Reduced (Literal (String (s ^ "\n" ^ l ^ "\n"), String))
                                | _ -> Stuck)
    (* Uninterpreted functions never reduce *)
    | Download -> (Primitive String, (* Path? URL? *)
                   Primitive String,
                   fun _ -> Stuck)
    | Template -> (Primitive String, Primitive String, fun _ -> Stuck)
    | GitClone -> (Primitive String, (* Path? URL? *)
                   Primitive String,
                   fun _ -> Stuck)

  let literalTyp : literal -> primTy = function
    | Unit   _ -> Unit
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Float  _ -> Float
    | String _ -> String
    | Path   _ -> Path
    | Env    _ -> Env

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
