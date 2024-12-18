open Calculus.Ast

exception NotImplemented

(* A 'a list2 is a list with at least two elements *)
type 'a list2 = LastTwo of 'a * 'a | Cons of 'a * 'a list2
type 'a list' = Nil | Singleton of 'a | List of 'a list2

module StringMap = Map.Make(String)

type prims      = Unit | Bool | Int | Float | String | Path | Env
type 't constr  = List of 't | Option of 't | Cases of 't list2
type 't func    = Proj          of bool * 't * 't   (* true = 1, false = 2 *)
                | Constructor   of bool * 't constr (* true = L, false = R *)
                | EmptyStruct   of 't StringMap.t
                | AddField      of 't StringMap.t * string
                | ReadField     of 't StringMap.t * string
                (* Name and input and output types *)
                | Uninterpreted of string * 't * 't
type ('v, 't) lit = Unit    of unit
                  | Bool    of bool
                  | Int     of int
                  | Float   of float
                  | String  of string
                  | Path    of string
                  | Env     of ('v * 't) StringMap.t

module rec Ast_Target : Ast_Defs
  with type variable  = string
  with type field     = string
  with type primTy    = prims
  with type namedTy   = Ast_Target.typ constr
  with type structTy  = Ast_Target.typ StringMap.t
  with type funct     = Ast_Target.typ func
  with type literal   = (Ast_Target.value, Ast_Target.typ) lit
  with type attribute = string * Ast_Target.typ
  with type element   = string * Ast_Target.typ
  with type action    = string * Ast_Target.typ * Ast_Target.typ
                      * Ast_Target.stmt option ref
= struct
  type primTy = prims

  type field = string
  module FieldMap = StringMap

  type namedTy = typ constr
  and structTy = typ FieldMap.t
  and typ = Product    of typ * typ
          | Primitive  of primTy
          | Named      of namedTy
          | Struct     of structTy

  type funct = typ func

  type variable = string
  module VariableMap = StringMap

  type literal = (value, typ) lit
   and record = value FieldMap.t
   and value = Unknown      of id * typ
             | Literal      of literal * primTy
             | Function     of funct * value * typ
             | Pair         of value * value * typ
             | Constructor  of namedTy * bool (* true = L, false = R *)
                             * value
             | Struct       of structTy * record

  type env = (value * typ) VariableMap.t

  type attribute = string * typ
  type element = string * typ

  type expr = Function  of funct * expr
            | Literal   of literal
            | Variable  of variable
            | Pair      of expr * expr
            | Env

  type qual = Attribute   of attribute * expr * qual list
            | Element     of element * expr * qual list
            | NotElement  of element * expr
  type attr = AttrAccess  of attribute
            | OnAttribute of attribute * attr
            | OnElement   of element * expr * attr
  type elem = Element     of element * expr
            | NotElement  of element * expr
            | OnAttribute of attribute * elem
            | OnElement   of element * expr * elem

  type action = string * typ * typ * stmt option ref
   and stmt = Action   of variable * action * expr * stmt
            | Assign   of variable * expr * stmt
            | Add      of qual * stmt
            | Get      of variable * attr * stmt
            | Contains of elem * stmt * stmt
            | Cond     of expr * stmt * stmt
            | Loop     of variable * expr * stmt * stmt
            | Match    of expr * variable * stmt * stmt
            | Fail     of string
            | Return   of expr

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Option t -> (Primitive Unit, t)
    | Cases (LastTwo (s, t)) -> (s, t)
    | Cases (Cons (s, ts)) -> (s, Named (Cases ts))
  let structTyDef fs = fs

  let funcDef = function
    | Proj (true, s, t)  -> (Product (s, t), s,
                             fun (v : value) ->
                               match v with Pair (x, _, _) -> Reduced x
                                          | _ -> Stuck)
    | Proj (false, s, t) -> (Product (s, t), t,
                             fun (v : value) ->
                               match v with Pair (_, y, _) -> Reduced y
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
                        fun _ -> Reduced (Struct (s, FieldMap.empty)))
    | AddField (s, f) -> (Product (Struct s, FieldMap.find f (structTyDef s)),
                          Struct s,
                          fun v -> match v with Pair (Struct (_, fs), x, _)
                                    -> Reduced (Struct (s, FieldMap.add f x fs))
                                   | _ -> Err "Add field failed to reduce")
    | ReadField (s, f) -> (Struct s, FieldMap.find f (structTyDef s),
                           fun v -> match v with Struct (_, fs)
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
    | (nm, in_typ, out_typ, def) ->
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
  let envToVal (env : env) : value = Literal (Env env, (Env : primTy))
  let envFromVal (v : value) =
    match v with Literal (Env env, _) -> env | _ -> failwith "Not environment"
end

module TargetInterp = Calculus.Interp.Interp(Ast_Target)

(* Debugging utilities *)

let rec string_of_expr (e : Ast_Target.expr) : string =
  match e with
  | Variable v         -> v
  | Literal (Unit ())  -> "()"
  | Literal (Bool b)   -> string_of_bool b
  | Literal (Int i)    -> string_of_int i
  | Literal (Float f)  -> string_of_float f
  | Literal (String s) -> "\"" ^ s ^ "\""
  | Literal (Path p)   -> "'" ^ p ^ "'"
  | Literal (Env _)    -> "%%SOME ENV%%"
  | Env                -> "%%ENV%%"
  | Pair (x, y)        ->
      "(" ^ string_of_expr x ^ ", " ^ string_of_expr y ^ ")"
  | Function (f, e) ->
      let string_f =
        match f with
        | Proj (true, _, _)         -> "proj1"
        | Proj (false, _, _)        -> "proj2"
        | Constructor (true, _)     -> "L"
        | Constructor (false, _)    -> "R"
        | EmptyStruct _             -> "{}"
        | AddField (_, field)       -> "add#" ^ field
        | ReadField (_, field)      -> "get#" ^ field
        | Uninterpreted (nm, _, _)  -> nm
      in string_f ^ "(" ^ string_of_expr e ^ ")"

let rec string_of_qual (q : Ast_Target.qual) : string =
  match q with
  | Attribute ((attr, _), e, qs) ->
      attr ^ " = " ^ string_of_expr e ^ " : < "
      ^ String.concat ", " (List.map string_of_qual qs) ^ " >"
  | Element ((elem, _), e, qs) ->
      elem ^ "(" ^ string_of_expr e ^ ") : < "
      ^ String.concat ", " (List.map string_of_qual qs) ^ " >"
  | NotElement ((elem, _), e) ->
      "!" ^ elem ^ "(" ^ string_of_expr e ^ ")"

let rec string_of_attr (a : Ast_Target.attr) : string =
  match a with
  | AttrAccess ((attr, _)) -> attr
  | OnAttribute ((attr, _), rest) -> attr ^ "." ^ string_of_attr rest
  | OnElement ((elem, _), e, rest) ->
      elem ^ "(" ^ string_of_expr e ^ ")." ^ string_of_attr rest

let rec string_of_elem (e : Ast_Target.elem) : string =
  match e with
  | Element ((elem, _), e) -> elem ^ "(" ^ string_of_expr e ^ ")"
  | NotElement ((elem, _), e) -> "!" ^ elem ^ "(" ^ string_of_expr e ^ ")"
  | OnAttribute ((attr, _), rest) ->
      attr ^ "." ^ string_of_elem rest
  | OnElement ((elem, _), e, rest) ->
      elem ^ "(" ^ string_of_expr e ^ ")." ^ string_of_elem rest

let string_of_stmt (s : Ast_Target.stmt) : string =
  let rec process (s : Ast_Target.stmt) (indent : string) : string =
    indent ^
    match s with
    | Action (v, (nm, _, _, _), arg, next) ->
        v ^ " = " ^ nm ^ "{" ^ string_of_expr arg ^ "}\n" ^ process next indent
    | Assign (v, e, next) ->
        v ^ " = " ^ string_of_expr e ^ "\n"               ^ process next indent
    | Add (q, next) ->
        "add " ^ string_of_qual q ^ "\n"                  ^ process next indent
    | Get (v, a, next) ->
        v ^ " = get " ^ string_of_attr a ^ "\n"           ^ process next indent
    | Contains (q, th, el) ->
        "contains " ^ string_of_elem q ^ " {\n"
        ^ process th ("\t" ^ indent)
        ^ indent ^ "} else {\n"
        ^ process el ("\t" ^ indent)
        ^ indent ^ "}\n"
    | Cond (e, th, el) ->
        "if " ^ string_of_expr e ^ "{\n"
        ^ process th ("\t" ^ indent)
        ^ indent ^ "} else {\n"
        ^ process el ("\t" ^ indent)
        ^ indent ^ "}\n"
    | Loop (v, lst, body, next) ->
        "foreach " ^ v ^ " in " ^ string_of_expr lst ^ " {\n"
        ^ process body ("\t" ^ indent)
        ^ indent ^ "}\n"
        ^ process next indent
    | Match (e, v, l, r) ->
        "match " ^ string_of_expr e ^ " with {\n"
        ^ indent ^ "\tL(" ^ v ^ ") => {\n"
        ^ process l ("\t\t" ^ indent)
        ^ indent ^ "\t}\n"
        ^ indent ^ "\tR(" ^ v ^ ") => {\n"
        ^ process r ("\t\t" ^ indent)
        ^ indent ^ "\t}\n"
    | Fail msg -> "fail \"" ^ msg ^ "\"\n"
    | Return e -> "return " ^ string_of_expr e ^ "\n"
  in process s ""

let rec value_to_string (v : Ast_Target.value) : string =
  match v with
  | Unknown (Loop x, _)   -> "?loop(" ^ string_of_int x ^ ")"
  | Unknown (Val x, _)    -> "?" ^ string_of_int x
  | Literal (Unit (), _)  -> "()"
  | Literal (Bool b, _)   -> string_of_bool b
  | Literal (Int i, _)    -> string_of_int i
  | Literal (Float f, _)  -> string_of_float f
  | Literal (String s, _) -> "\"" ^ s ^ "\""
  | Literal (Path p, _)   -> "'" ^ p ^ "'"
  | Literal (Env _, _)    -> "%%ENV%%"
  | Pair    (x, y, _)     ->
      "(" ^ value_to_string x ^ ", " ^ value_to_string y ^ ")"
  | Constructor (_, left, v) ->
      (if left then "L(" else "R(") ^ value_to_string v ^ ")"
  | Struct (_, r) ->
      "{" ^ String.concat ", "
              (List.map (fun (nm, v) -> nm ^ ": " ^ value_to_string v)
                (Ast_Target.FieldMap.to_list r))
          ^ "}"
  | Function (f, arg, _)  ->
      match f with
      | Proj (true, _, _)         -> "proj1(" ^ value_to_string arg ^ ")"
      | Proj (false, _, _)        -> "proj2(" ^ value_to_string arg ^ ")"
      | Uninterpreted (nm, _, _)  -> nm ^ "(" ^ value_to_string arg ^ ")"
      | _ -> "%%FUNCTION%%(" ^ value_to_string arg ^ ")"

let rec state_to_string (state : TargetInterp.state) : string =
  let State(elems, attrs) = state
  in Printf.sprintf "< %s >"
    (String.concat ", "
      (List.map
        (fun (((elem, _), v, neg), s) ->
          (if neg then "not " else "")
          ^ elem ^ "(" ^ value_to_string v ^ ")"
          ^ ": " ^ state_to_string s)
        (TargetInterp.ElementMap.to_list elems)
      @
      List.map
        (fun ((attr, _), (v, s)) -> attr ^ " = " ^ value_to_string v
                                 ^ ": " ^ state_to_string s)
        (TargetInterp.AttributeMap.to_list attrs)))

let prg_type_to_string (state : TargetInterp.prg_type) : string =
  Printf.sprintf "%s --> %s [{ %s }, { %s }, { %s }]"
    (state_to_string state.init)
    (state_to_string state.final)
    (String.concat ", "
      (List.map (fun (v, i) -> value_to_string v ^ ": #" ^ string_of_int i)
        (TargetInterp.ValueMap.to_list state.loops)))
    (String.concat ", "
      (List.map (fun (v, b) -> value_to_string v ^ " = " ^ string_of_bool b)
        (TargetInterp.ValueMap.to_list state.bools)))
    (String.concat ", "
      (List.map (fun (v, (b, w)) -> value_to_string v ^ " = "
                  ^ (if b then "L" else "R") ^ "(" ^ value_to_string w ^ ")")
        (TargetInterp.ValueMap.to_list state.constrs)))

let results_to_string (res : TargetInterp.prg_res list) : string =
  let rec process (res : TargetInterp.prg_res list) : string list * string list =
    match res with
    | [] -> ([], [])
    | Err msg :: tl ->
        let (succs, fails) = process tl
        in (succs, msg :: fails)
    | Ok (state, returned) :: tl ->
        let (succs, fails) = process tl
        in let state_str = prg_type_to_string state
        in let value_str = value_to_string returned
        in ((state_str ^ " returned " ^ value_str) :: succs, fails)
  in match process res with
  | ([], errors) ->
      "All branches of computation failed:\n" ^ String.concat "\n" errors
  | (states, _) -> String.concat "\n" states
