open Calculus.Ast

(* A 'a list2 is a list with at least two elements *)
type 'a list2 = LastTwo of 'a * 'a | Cons of 'a * 'a list2
type 'a list' = Nil | Singleton of 'a | List of 'a list2

module StringMap = Map.Make(String)

type prims      = Unit | Bool | Int | Float | String | Path | Env
type 't constr  = List of 't | Option of 't
                (* For all other enums we store the name of the enum and the
                 * name of each constructor *)
                | Cases of string * (string * 't) list2
type 't func    = Proj          of bool * 't * 't   (* true = 1, false = 2 *)
                | Constructor   of bool * 't constr (* true = L, false = R *)
                | EmptyStruct   of 't StringMap.t
                | AddField      of 't StringMap.t * string
                | ReadField     of 't StringMap.t * string
                | BoolNeg
                | Concat
                | Equal         of 't
                (* Path operations *)
                | ConsPath
                | PathOfString
                | StringOfPath
                | EndsWithDir
                | BaseName
                | PathFrom
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
             | Constructor  of namedTy * bool * value
             | Struct       of structTy * record
             | ListVal      of namedTy * value

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
            | Match    of expr * variable * stmt * stmt
            | ForEach  of variable * typ * expr * variable * stmt * stmt
            | Fail     of string
            | Return   of expr

  type values_equal_res = Yes | No | Unsure
  let rec values_equal x y : values_equal_res =
    match x, y with
    | Unknown (x, _), Unknown (y, _) -> if x = y then Yes else Unsure
    | Unknown (_, _), _ | _, Unknown (_, _) -> Unsure

    | Literal (x, _), Literal (y, _) -> if x = y then Yes else No

    | Function (fx, vx, _), Function (fy, vy, _) when fx = fy ->
        begin match values_equal vx vy with
        | Yes -> Yes
        | _ -> Unsure
        end
    | Function (_, _, _), _ | _, Function (_, _, _) -> Unsure

    | Pair (xa, xb, _), Pair (ya, yb, _) ->
        begin match values_equal xa ya, values_equal xb yb with
        | No, _ | _, No -> No
        | Unsure, _ | _, Unsure -> Unsure
        | Yes, Yes -> Yes
        end

    | Constructor (_, cx, vx), Constructor (_, cy, vy) ->
        if cx <> cy then No else values_equal vx vy

    | Struct (_, xs), Struct (_, ys) ->
        (* Collect the bindings where xs and ys are not (necessarily) equal
         * (possibly because only one of them defines it) *)
        let diffs =
          FieldMap.merge (fun _ x_val y_val ->
            match x_val, y_val with
            | Some x, Some y ->
                begin match values_equal x y with
                | Yes -> None
                | Unsure -> Some Unsure
                | No -> Some No
                end
            | _, _ -> Some No)
            xs ys
        in if FieldMap.is_empty diffs
        then Yes (* nothing in the diffs means all bindings are equal *)
        else if FieldMap.exists (fun _ v -> v = No) diffs
        then No
        else Unsure

    | ListVal (_, vx), ListVal (_, vy) -> values_equal vx vy

    | ListVal (_, _), Constructor (_, _, _)
    | Constructor (_, _, _), ListVal (_, _) -> Unsure

    | Literal (_, _), Pair (_, _, _)
    | Literal (_, _), Constructor (_, _, _)
    | Literal (_, _), Struct (_, _)
    | Literal (_, _), ListVal (_, _)
    | Pair (_, _, _), Literal (_, _)
    | Pair (_, _, _), Constructor (_, _, _)
    | Pair (_, _, _), Struct (_, _)
    | Pair (_, _, _), ListVal (_, _)
    | Constructor (_, _, _), Literal (_, _)
    | Constructor (_, _, _), Pair (_, _, _)
    | Constructor (_, _, _), Struct (_, _)
    | Struct (_, _), Literal (_, _)
    | Struct (_, _), Pair (_, _, _)
    | Struct (_, _), Constructor (_, _, _)
    | Struct (_, _), ListVal (_, _)
    | ListVal (_, _), Literal (_, _)
    | ListVal (_, _), Pair (_, _, _)
    | ListVal (_, _), Struct (_, _) ->
        failwith "Attempted to compare values that are of different types"

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Option t -> (Primitive Unit, t)
    | Cases (_, LastTwo ((_, s), (_, t))) -> (s, t)
    | Cases (nm, Cons ((_, s), ts)) -> (s, Named (Cases (nm, ts)))
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
    | BoolNeg -> (Primitive Bool, Primitive Bool,
        fun v -> match v with Literal (Bool b, _)
                    -> Reduced (Literal (Bool (not b), Bool))
                 | _ -> Stuck)
    | Concat -> (Product (Primitive String, Primitive String),
                 Primitive String,
        fun v -> match v with
          | Pair (Literal (String p, _), Literal (String q, _), _)
            -> Reduced (Literal (String (p ^ q), String))
          | _ -> Stuck)
    | Equal t -> (Product (t, t), Primitive Bool,
        fun v -> match v with
          | Pair (x, y, _) ->
              begin match values_equal x y with
              | Yes -> Reduced (Literal (Bool true, Bool))
              | No  -> Reduced (Literal (Bool false, Bool))
              | Unsure -> Stuck
              end
          | _ -> Stuck)
    | ConsPath -> (Product (Primitive Path, Primitive Path),
                   Primitive Path,
        fun v -> match v with
          | Pair (Literal (Path p, _), Literal (Path q, _), _)
            -> Reduced (Literal (Path (p ^ "/" ^ q), Path))
          | _ -> Stuck)
    | PathOfString -> (Primitive String, Primitive Path,
        fun v -> match v with
          | Literal (String s, _) -> Reduced (Literal (Path s, Path))
          | _ -> Stuck)
    | StringOfPath -> (Primitive Path, Primitive String,
        fun v -> match v with
          | Literal (Path s, _) -> Reduced (Literal (String s, String))
          | _ -> Stuck)
    | EndsWithDir -> (Primitive Path, Primitive Bool,
        fun v -> match v with
          | Literal (Path p, _)
            -> let lastChar = String.sub p (String.length p - 1) 1
               in let res = lastChar = "/"
               in Reduced (Literal (Bool res, Bool))
          | _ -> Stuck)
    | BaseName -> (Primitive Path, Primitive Path,
        fun v -> match v with
          | Literal (Path p, _)
            -> Reduced (Literal (Path (Filename.basename p), Path))
          | _ -> Stuck)
    | PathFrom -> (Product (Primitive Path, Primitive Path),
                   Primitive Path,
        fun v -> match v with
          | Pair (Literal (Path base, _), Literal (Path full, _), _)
            -> if String.sub full 0 (String.length base) = base
               then
                 let res = String.sub full (String.length base) (String.length full - String.length base)
                 in Reduced (Literal (Path res, Path))
               else Err "The base path in path_from must be the base of the full path"
          | _ -> Stuck)
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

  let boolAsValue (b: bool) : value = Literal (Bool b, Bool)

  let isUnit (t : typ) : bool =
    match t with
    | Primitive Unit -> true
    | _ -> false
  let listType (t : typ) : namedTy = List t

  let envType : typ = Primitive Env
  let envToVal (env : env) : value = Literal (Env env, (Env : primTy))
  let envFromVal (v : value) =
    match v with Literal (Env env, _) -> env | _ -> failwith "Not environment"

  type constr = IsBool of bool | IsConstructor of bool * (id * typ)
  type result_constraint = IsBool        of value * bool
                         | IsConstructor of value * (bool * (id * typ))
                         | IsEqual       of id * value
  type func_constraints = Unreducible | Reducible of result_constraint list list

  (* Reductions of constraints can leave out any reductions that are handled by
   * the actual definitions, like proj1(pair(x, y)), that will already have
   * simplified by this point and so if we get proj1(x) at this point that means
   * we can't do anything *)
  let reduceFuncConstraint (f: funct) (v: value) (c: constr) =
    match f, c with
    | BoolNeg, IsBool b -> Reducible [[ IsBool (v, not b) ]]
    | Equal _, IsBool true ->
        begin match v with
        | Pair (Unknown (x, _), y, _) -> Reducible [[ IsEqual (x, y) ]]
        | Pair (x, Unknown (y, _), _) -> Reducible [[ IsEqual (y, x) ]]
        | _ -> Unreducible
        end
    | _, _ -> Unreducible
end

module TargetInterp = Calculus.Interp.Interp(Ast_Target)

(* Display utilities *)
let rec string_of_type (t : Ast_Target.typ) : string =
  match t with
  | Product (x, y)   -> Printf.sprintf "(%s, %s)" (string_of_type x) (string_of_type y)
  | Primitive Unit   -> "()"
  | Primitive Bool   -> "bool"
  | Primitive Int    -> "int"
  | Primitive Float  -> "float"
  | Primitive String -> "string"
  | Primitive Path   -> "path"
  | Primitive Env    -> "env"
  | Struct tys       ->
      Printf.sprintf "{ %s }"
        (String.concat ", "
          (List.map (fun (nm, t) -> nm ^ ": " ^ string_of_type t)
            (StringMap.to_list tys)))
  | Named (List t)   -> Printf.sprintf "list<%s>" (string_of_type t)
  | Named (Option t) -> Printf.sprintf "option<%s>" (string_of_type t)
  | Named (Cases (nm, _)) -> nm

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
        | BoolNeg                   -> "not"
        | Concat                    -> "concat"
        | Equal _                   -> "equal"
        | ConsPath                  -> "cons_path"
        | PathOfString              -> "path_of_string"
        | StringOfPath              -> "string_of_path"
        | EndsWithDir               -> "ends_with_dir"
        | BaseName                  -> "base_name"
        | PathFrom                  -> "path_from"
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
    | Match (e, v, l, r) ->
        "match " ^ string_of_expr e ^ " with {\n"
        ^ indent ^ "\tL(" ^ v ^ ") => {\n"
        ^ process l ("\t\t" ^ indent)
        ^ indent ^ "\t}\n"
        ^ indent ^ "\tR(" ^ v ^ ") => {\n"
        ^ process r ("\t\t" ^ indent)
        ^ indent ^ "\t}\n"
        ^ indent ^ "}\n"
    | ForEach (v, _, lst, w, body, next) ->
        v ^ " = foreach " ^ w ^ " in " ^ string_of_expr lst ^ " {\n"
        ^ process body ("\t" ^ indent)
        ^ indent ^ "};\n"
        ^ process next indent
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
  | Constructor (ty, left, v) ->
      begin match ty with
      | List t ->
          if left
          then Printf.sprintf "nil::<%s>()" (string_of_type t)
          else Printf.sprintf "list::<%s>[%s]" (string_of_type t) (string_of_list_val v)
      | Option t ->
          if left
          then Printf.sprintf "None::<%s>()" (string_of_type t)
          else Printf.sprintf "Some::<%s>(%s)" (string_of_type t) (value_to_string v)
      | Cases (enum, constrs) ->
          string_of_constructor enum constrs left v
      end
  | Struct (_, r) ->
      "{" ^ String.concat ", "
              (List.map (fun (nm, v) -> nm ^ ": " ^ value_to_string v)
                (Ast_Target.FieldMap.to_list r))
          ^ "}"
  | ListVal (_, v) -> "list { " ^ value_to_string v ^ " }"
  | Function (f, arg, _)  ->
      match f with
      | Proj (true, _, _)         -> "proj1(" ^ value_to_string arg ^ ")"
      | Proj (false, _, _)        -> "proj2(" ^ value_to_string arg ^ ")"
      | BoolNeg                   -> "not(" ^ value_to_string arg ^ ")"
      | Concat                    -> "concat(" ^ value_to_string arg ^ ")"
      | Equal _                   -> "equal(" ^ value_to_string arg ^ ")"
      | ConsPath                  -> "cons_path(" ^ value_to_string arg ^ ")"
      | PathOfString              -> "path_of_string(" ^ value_to_string arg ^ ")"
      | StringOfPath              -> "string_of_path(" ^ value_to_string arg ^ ")"
      | EndsWithDir               -> "ends_with_dir(" ^ value_to_string arg ^ ")"
      | BaseName                  -> "base_name(" ^ value_to_string arg ^ ")"
      | PathFrom                  -> "path_from(" ^ value_to_string arg ^ ")"
      | Uninterpreted (nm, _, _)  -> nm ^ "(" ^ value_to_string arg ^ ")"
      | _ -> "%%FUNCTION%%(" ^ value_to_string arg ^ ")"
and string_of_list_val (v : Ast_Target.value) : string =
  match v with
  | Pair (hd, tl, _) ->
      value_to_string hd
      ^ begin match tl with
        | Constructor (_, is_nil, lst) ->
            if is_nil then "" else "; " ^ string_of_list_val lst
        | Unknown (_, _) -> ";" ^ value_to_string v ^ " ..."
        | _ -> "; <<ERROR: MALFORMED LIST>>"
        end
  | Unknown (_, _) -> value_to_string v ^ " ..."
  | _ -> "<<ERROR: MALFORMED LIST>>"
and string_of_constructor enum constr is_first v =
  match constr, is_first with
  | LastTwo ((nm, _), _), true
  | Cons    ((nm, _), _), true
    -> enum ^ "::" ^ nm ^ "(" ^ value_to_string v ^ ")"
  | LastTwo (_, (nm, _)), false
    -> enum ^ "::" ^ nm ^ "(" ^ value_to_string v ^ ")"
  | Cons (_, cs), false
    -> match v with
       | Constructor (_, is_first, v) -> string_of_constructor enum cs is_first v
       | Unknown (_, _) -> value_to_string v
       | _ -> "<< ERROR: MALFORMED ENUM VALUE >>"

let string_of_list empty lhs sep rhs f lst : string =
  if List.is_empty lst
  then empty
  else lhs ^ String.concat sep (List.map f lst) ^ rhs

let state_to_string (state : TargetInterp.state) : string =
  let rec inner_string_of_state if_empty lhs rhs (state : TargetInterp.state) =
    let State(elems, attrs) = state
    in string_of_list if_empty lhs ", " rhs (fun s -> s)
        (List.map
          (fun (((elem, _), v, neg), s) ->
            (if neg then "not " else "")
            ^ elem ^ "(" ^ value_to_string v ^ ")"
            ^ inner_string_of_state "" ": <" " >" s)
          (TargetInterp.ElementMap.to_list elems)
        @
        List.map
          (fun ((attr, _), (v, s)) -> attr ^ " = " ^ value_to_string v
                                   ^ inner_string_of_state "" ": < " " >" s)
          (TargetInterp.AttributeMap.to_list attrs))
  in inner_string_of_state "<>" "< " " >" state

let string_of_constructor_constraint (v: Ast_Target.value) (left: bool)
  (arg: Ast_Target.value) : string =
  let ty : Ast_Target.typ = TargetInterp.val_to_type v
  in value_to_string v ^ " = " ^
  match ty with
  | Named ty ->
      begin match ty with
      | List t ->
          if left
          then Printf.sprintf "nil::<%s>()" (string_of_type t)
          else Printf.sprintf "list::<%s>[%s]" (string_of_type t) (string_of_list_val arg)
      | Option t ->
          if left
          then Printf.sprintf "None::<%s>()" (string_of_type t)
          else Printf.sprintf "Some::<%s>(%s)" (string_of_type t) (value_to_string arg)
      | Cases (enum, constrs) ->
          string_of_constructor enum constrs left arg
      end
  | _ -> "<< ERROR: MALFORMED CONSTRUCTOR CONSTRAINT >>"

let string_of_loop_info (i: TargetInterp.loop_info) : string =
  match i with
  | AllUnknown i -> "#" ^ string_of_int i
  | AllKnown v -> value_to_string v
  | LastKnown (i, v) -> "#" ^ string_of_int i ^ "/" ^ value_to_string v

let prg_type_to_string (state : TargetInterp.prg_type) : string =
  Printf.sprintf "%s --> %s [{ %s }, { %s }, { %s }]"
    (state_to_string state.init)
    (state_to_string state.final)
    (String.concat ", "
      (List.map (fun (v, i) -> value_to_string v ^ ": " ^ string_of_loop_info i)
        (TargetInterp.ValueMap.to_list state.loops)))
    (String.concat ", "
      (List.map (fun (v, b) -> value_to_string v ^ " = " ^ string_of_bool b)
        (TargetInterp.ValueMap.to_list state.bools)))
    (String.concat ", "
      (List.map (fun (v, (b, w)) -> string_of_constructor_constraint v b w)
        (TargetInterp.ValueMap.to_list state.constrs)))

let results_to_string (res : TargetInterp.prg_res list) : (string, string) result =
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
  | ([], errors) -> Error(String.concat "\n" errors)
  | (states, _) -> Ok(String.concat "\n" states)
