(* TODO: Fix error handling *)

type 'a list2 = 'a Target.list2

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module Target = Target.Ast_Target

module UniqueMap = struct
  type 'a t = (string, 'a) Hashtbl.t

  let empty () = Hashtbl.create 10

  let find (key : string) (map : 'a t) : 'a option =
    Hashtbl.find_opt map key

  let add (key : string) (value : 'a) (map : 'a t) : unit =
    match find key map with
    | Some _ -> failwith (Printf.sprintf "key %s already defined" key)
    | _ -> Hashtbl.add map key value
end

let array_foldr1 (arr : 'a array) (f : 'a -> 'a -> 'a) : 'a =
  let rec process (i : int) : 'a =
    if i + 1 = Array.length arr
    then arr.(i)
    else f arr.(i) (process (i+1))
  in process 0

type 'a placeholder = 'a option ref

type typ = Bool | Int | Float | String | Path | Unit
         | Option      of typ
         | List        of typ
         | Product     of typ list
         | Struct      of typ StringMap.t
         | Enum        of (int * typ list) StringMap.t
         | Placeholder of typ placeholder

let rec type_equality (x : typ) (y : typ) : bool =
  match x, y with
  | Placeholder { contents = Some x }, _ -> type_equality x y
  | _, Placeholder { contents = Some y } -> type_equality x y
  | _, _ -> x = y

type module_info =
  { name : string list;
    (* Alias map maps from aliases to their canonical name *)
    alias_map : string StringMap.t;
    argument_types : typ StringMap.t;
    input_struct_def : typ StringMap.t;
    out_type : typ;
    body : Target.stmt placeholder }

type type_env = typ UniqueMap.t

let rec extract_enum (t : typ) : (int * typ list) StringMap.t =
  match t with
  | Enum res -> res
  | Option t ->
      StringMap.of_list [("nothing", (0, [])); ("some", (1, [t]))]
  | List t ->
      StringMap.of_list [("nil", (0, [])); ("cons", (1, [t; List t]))]
  | Placeholder { contents  = Some t } -> extract_enum t
  | _ -> failwith "Not an enum type"

let lookup_enum (tys : type_env) (nm : string)
  : (int * typ list) StringMap.t =
    match UniqueMap.find nm tys with
    | None -> failwith "Undefined type"
    | Some t -> extract_enum t

type env_entry = Attribute of string * typ
               | Element of string * typ
               | Uninterpreted of string * typ list * typ
               (* Function has its argument type and then return type *)
               | Function of string * Target.typ * typ * Target.stmt placeholder
               | Module of module_info
               (* Environment is used to create a multi-level environment to
                * handle fully qualified names *)
               | Environment of global_env
and global_env = env_entry UniqueMap.t

let rec add_modules (nm : string list) (t : env_entry) env : unit =
  match nm with
  | [] -> failwith "Empty module name"
  | [n] -> UniqueMap.add n t env
  | n :: tl ->
      match UniqueMap.find n env with
      | Some (Environment env) -> add_modules tl t env
      | Some _ -> failwith "Name already exists"
      | None ->
          let new_env = UniqueMap.empty ()
          in UniqueMap.add n (Environment new_env) env
          ; add_modules tl t new_env

let rec create_type (t : Ast.typ) env : typ =
  match t with
  | Bool -> Bool
  | Int -> Int
  | Float -> Float
  | String -> String
  | Path -> Path
  | Unit -> Unit
  | Product ts -> Product (List.map (fun t -> create_type t env) ts)
  | List t -> List (create_type t env)
  | Named nm ->
      match UniqueMap.find nm env with
      | Some t -> t
      | None ->
          let res = Placeholder (ref None)
          in UniqueMap.add nm res env; res

let create_types_option (ts : Ast.typ list option) env : typ list =
  match ts with
  | None -> []
  | Some ts -> List.map (fun t -> create_type t env) ts

(* process_type (unlike create_type) fails if a named type is not defined *)
let rec process_type (t : Ast.typ) env : typ =
  match t with
  | Bool -> Bool
  | Int -> Int
  | Float -> Float
  | String -> String
  | Path -> Path
  | Unit -> Unit
  | Product ts -> Product (List.map (fun t -> process_type t env) ts)
  | List t -> List (process_type t env)
  | Named nm ->
      match UniqueMap.find nm env with
      | Some t -> t
      | None -> failwith (Printf.sprintf "undefined type %s" nm)

let process_type_option (t : Ast.typ option) env : typ =
  match t with
  | None -> Unit
  | Some t -> process_type t env

let process_module_for_args (body : Ast.stmt list) env
  : string StringMap.t * typ StringMap.t * typ StringMap.t = 
  let rec add_alias alias nm aliases =
    match alias with
    | [] -> aliases
    | v :: tl ->
        match StringMap.find_opt v aliases with
        | None -> add_alias tl nm (StringMap.add v nm aliases)
        | Some n ->
            if n = nm then add_alias tl nm aliases
            else failwith "variable already used as alias with different canonical name"
  in let rec add_vars vars aliases var_types struct_def =
    match vars with
    | [] -> (aliases, var_types, struct_def)
    | (nm, alias, typ, _) :: tl ->
        let typ = process_type typ env
        in let var_types =
          match StringMap.find_opt nm aliases with
          | Some _ -> failwith "variable already used as alias"
          | None ->
              match StringMap.find_opt nm var_types with
              | None -> StringMap.add nm typ var_types
              | Some t ->
                  if type_equality t typ then var_types
                  else failwith "variable already used with incompatible types"
        in let aliases = add_alias alias nm aliases
        in let struct_def = StringMap.add nm (Option typ) struct_def
        in add_vars tl aliases var_types struct_def
  in let rec process (body : Ast.stmt list) aliases var_types struct_def =
    match body with
    | [] -> (aliases, var_types, struct_def)
    | RequiredVar vars :: tl | OptionalVar vars :: tl ->
        let (aliases, var_types, struct_def)
          = add_vars vars aliases var_types struct_def
        in process tl aliases var_types struct_def
    | ForLoop (_, _, body) :: tl ->
        let (aliases, var_types, struct_def)
          = process body aliases var_types struct_def
        in process tl aliases var_types struct_def
    | IfProvided (_, thn, els) :: tl | IfThenElse (_, thn, els) :: tl ->
        let (aliases, var_types, struct_def)
          = process thn aliases var_types struct_def
        in let (aliases, var_types, struct_def)
          = process els aliases var_types struct_def
        in process tl aliases var_types struct_def
    | Match (_, cases) :: tl ->
        List.fold_left
          (fun (aliases, var_types, struct_def) (_, case)
            -> process case aliases var_types struct_def)
          (process tl aliases var_types struct_def)
          cases
    | _ :: tl -> process tl aliases var_types struct_def
  in process body StringMap.empty StringMap.empty StringMap.empty

(* Convert an internal type into a target type *)
let rec target_type (t : typ) : Target.typ =
  match t with
  | Bool -> Primitive Bool
  | Int -> Primitive Int
  | Float -> Primitive Float
  | String -> Primitive String
  | Path -> Primitive Path
  | Unit -> Primitive Unit
  | Option t -> Named (Option (target_type t))
  | List t -> Named (List (target_type t))
  | Product ts -> construct_prod ts
  | Struct fs -> Struct (StringMap.map target_type fs)
  | Enum _cs -> Primitive Unit (*construct_cases cs*)
  | Placeholder t ->
      match !t with
      | None -> failwith "Missing type definition"
      | Some t -> target_type t
and construct_prod (ts : typ list) : Target.typ =
  match ts with
  | [] -> Primitive Unit
  | [t] -> target_type t
  | t :: ts -> Product (target_type t, construct_prod ts)

let rec to_list2 (xs : 'a list) : 'a list2 option =
  match xs with
  | [] | _ :: [] -> None
  | x :: y :: [] -> Some (LastTwo (x, y))
  | x :: xs ->
      match to_list2 xs with
      | Some xs -> Some (Cons (x, xs))
      | None -> failwith "BUG in to_list2"

(* get_enum_info takes the type environment, enum name, and constructor name
 * and returns:
 * - Left (named, index) if nm defines a multi-constructor enum and named is
 *   the named type defining this enum and index is the constructor's index
 * - Right typ if nm defines a single-constructor enum, and typ is the type
 *   of the constructor
 *)
let get_enum_info (tys : type_env) (nm : string) (constr : string)
  : (Target.namedTy * int, Target.typ) Either.t =
  let rec extract_enum_info (t : typ)
    : (Target.namedTy * int , Target.typ) Either.t =
    match t with
    | Enum constrs ->
        begin match StringMap.find_opt constr constrs with
        | None -> failwith "Invalid constructor"
        | Some (idx, tys) -> 
            if StringMap.cardinal constrs = 1
            then Either.Right (target_type (Product tys))
            else let cases : Target.typ Array.t 
              = Array.make (StringMap.cardinal constrs) (Target.Primitive Unit)
            in StringMap.iter
              (fun _ (idx, tys) -> cases.(idx) <- target_type (Product tys))
              constrs
            ; match to_list2 (Array.to_list cases) with
            | None -> failwith "enum does not have enough cases"
            | Some cs -> Either.Left (Cases cs, idx)
        end
    | Option t     ->
        let typ = target_type t
        in if constr = "nothing"
        then Either.Left (Option typ, 0)
        else if constr = "some"
        then Either.Left (Option typ, 1)
        else failwith "Invalid constructor of option"
    | List t       ->
        let typ = target_type t
        in if constr = "nil"
        then Either.Left (List typ, 0)
        else if constr = "cons"
        then Either.Left (List typ, 1)
        else failwith "Invalid constructor of list"
    | Placeholder { contents = Some t } -> extract_enum_info t
    | _ -> failwith "Not an enum type"
  in match UniqueMap.find nm tys with
  | Some t -> extract_enum_info t
  | None -> failwith "undefined type"

(* construct_enum generates the constructors needed for an enum constructor
 * identified by the given named type and constructor index *)
let construct_enum (enum : Target.namedTy) (idx : int) (e : Target.expr)
  : Target.expr =
  let rec construct_cases (cs : Target.typ list2) (idx : int) : Target.expr =
    match cs with
    | LastTwo (_, _) ->
        if idx = 0 then Function (Constructor (true, Cases cs), e)
        else if idx = 1 then Function (Constructor (true, Cases cs), e)
        else failwith "internal error: invalid index for enum"
    | Cons (_, r) ->
        if idx = 0 then Function (Constructor (true, Cases cs), e)
        else Function (Constructor (false, Cases cs), construct_cases r (idx-1))
  in match enum with
  | List _ | Option _ ->
      if idx = 0 then Function (Constructor (true, enum), e)
      else if idx = 1 then Function (Constructor (false, enum), e)
      else failwith "internal error: invalid index for list or option"
  | Cases cs -> construct_cases cs idx

(* The result of our internal expression processing *)
type expr_result = JustExpr of Target.expr
                 | JustAttr of (Target.attr -> Target.attr)
                 | ExprOrAttr of Target.expr * (Target.attr -> Target.attr)

(* TODO *)
(* process_expr takes a continuation which takes an expression and produces a
 * statement and then returns a statement. The reason for this is that some
 * expressions in the Module language requires statmenets in the calculus and
 * so we may have to build statments as we process the expression.  This setup
 * will be placed before the statement generated by the continuation which can
 * use the result of the expression *)
let process_expr (e : Ast.expr) _env tys (k : Target.expr -> Target.stmt)
  : Target.stmt =
  (* Our main helper function; it's continuation takes an "expr_result" which
   * contains at least one of an expression and a function to produce an
   * attribute; this is because of how we need to evaluate attributes. The
   * possibility of both an expression and attribute is needed to handle
   * attributes on attributes *)
  let rec process (e : Ast.expr) (k : expr_result -> Target.stmt)
    : Target.stmt =
    match e with
    | Id nm       -> k (JustExpr (Variable nm))
    | BoolLit v   -> k (JustExpr (Literal (Bool v)))
    | IntLit v    -> k (JustExpr (Literal (Int v)))
    | FloatLit v  -> k (JustExpr (Literal (Float v)))
    | StringLit v -> k (JustExpr (Literal (String v)))
    | UnitExp     -> k (JustExpr (Literal (Unit ())))
    | ProductExp es ->
        begin match es with
        | [] -> k (JustExpr (Literal (Unit ())))
        | [e] -> process e k
        | e :: es -> 
            process e
              (fun e ->
                match e with
                | JustExpr e | ExprOrAttr (e, _)
                -> process (ProductExp es)
                  (fun es ->
                    match es with
                    | JustExpr es | ExprOrAttr (es, _)
                    -> k (JustExpr (Pair (e, es)))
                    | _ -> failwith "expected expression")
                | _ -> failwith "expected expression")
        end
    | RecordExp (nm, fields) ->
        begin match nm with
        | Id nm ->
            begin match UniqueMap.find nm tys with
            | Some (Struct struct_def) ->
                let target_struct = StringMap.map target_type struct_def
                in let init_struct : Target.expr
                  = Function (EmptyStruct target_struct, Literal (Unit ()))
                in let filled_struct : Target.expr -> Target.stmt
                  = List.fold_left 
                    (fun (k : Target.expr -> Target.stmt) (field, expr) record ->
                      if not (StringMap.mem field struct_def)
                      then failwith "unexpected field"
                      else
                        process expr
                          (fun field_expr ->
                            match field_expr with
                            | JustExpr e | ExprOrAttr (e, _)
                            -> k (Function (AddField (target_struct, field),
                                Pair (record, e)))
                            | _ -> failwith "expected expression"))
                    (fun e -> k (JustExpr e))
                    fields
                in filled_struct init_struct
            | _ -> failwith "expected struct name"
            end
        | _ -> failwith "expected struct name"
        end
    | EnumExp (enum, constr, args) ->
        begin match enum with
        | Id enum ->
            begin match get_enum_info tys enum constr with
            | Either.Left (enum, idx) ->
                process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr e | ExprOrAttr (e, _) ->
                        k (JustExpr (construct_enum enum idx e))
                    | _ -> failwith "expected expression")
            | Either.Right _ -> process (ProductExp args) k
            end
        | _ -> failwith "expected enum name"
        end
    | FuncExp (func, args) ->
        begin match func with
        | Id nm -> failwith "TODO"
        | Field (qual, elem) -> failwith "TODO"
        | _ -> failwith "invalid function expression"
        end
    | _ -> failwith "TODO"
  in process e
    (fun e -> match e with
              | JustExpr e | ExprOrAttr (e, _) -> k e
              | JustAttr _ -> failwith "Expected expression, not element")

let rec process_qual (e : Ast.expr) env tys (q : Target.qual)
  (k : Target.qual -> Target.stmt) : Target.stmt =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
              (fun expr -> k (Element (elem, expr, [q])))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
            (fun expr ->
              process_qual qual env tys (Element (elem, expr, [q])) k)
      | _ -> failwith "Invalid element"
      end
  | Field (qual, attr) ->
      begin match UniqueMap.find attr env with
      | Some (Attribute (nm, typ)) ->
          let attr = (nm, target_type typ)
          (* By processing the current expression we produce the current value
           * of the attribute *)
          in process_expr e env tys
            (fun expr ->
              process_qual qual env tys (Attribute (attr, expr, [q])) k)
      | _ -> failwith "Invalid attribute"
      end
  | _ -> failwith "Invalid qualifier"

(* Process an expression for a clear statement (the final access is not an
   attribute) *)
let process_expr_as_qual (e : Ast.expr) env tys (k : Target.qual -> Target.stmt) 
  : Target.stmt =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
              (fun expr -> k (Element (elem, expr, [])))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
            (fun expr ->
              process_qual qual env tys (Element (elem, expr, [])) k)
      | _ -> failwith "Invalid element"
      end
  | _ -> failwith "Invalid qualifier"

let rec negate_qual (q : Target.qual) : Target.qual =
  match q with
  | Attribute (_, _, []) -> failwith "Cannot negate an attribute"
  | Attribute (a, e, qs) -> Attribute (a, e, List.map negate_qual qs)
  | Element (e, ex, []) -> NotElement (e, ex)
  | Element (e, ex, qs) -> Element (e, ex, List.map negate_qual qs)
  | NotElement (_, _) -> failwith "Cannot generate negated qual from front-end"

let process_expr_as_elem (e : Ast.expr) env tys (k : Target.elem -> Target.stmt)
  : Target.stmt =
  let rec process_elem (q : Ast.expr) (e : Target.elem)
    (k : Target.elem -> Target.stmt) : Target.stmt =
    match q with
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys
                (fun expr -> k (OnElement (elem, expr, e)))
        | _ -> failwith "Invalid element"
        end
    | FuncExp (Field (qual, elem), args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys
              (fun expr ->
                process_elem qual (OnElement (elem, expr, e)) k)
        | _ -> failwith "Invalid element"
        end
    | Field (qual, attr) ->
        begin match UniqueMap.find attr env with
        | Some (Attribute (nm, typ)) ->
            let attr = (nm, target_type typ)
            in process_elem qual (OnAttribute (attr, e)) k
        | _ -> failwith "Invalid attribute"
        end
    | _ -> failwith "Invalid qualifier"
  in match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
              (fun expr -> k (Element (elem, expr)))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys
            (fun expr -> process_elem qual (Element (elem, expr)) k)
      | _ -> failwith "Invalid element"
      end
  | _ -> failwith "Invalid qualifier"

(* L-values are only variables and attributes in the state *)
let process_expr_as_lval (e : Ast.expr) env tys (assign : Target.expr)
  (k : Target.stmt) : Target.stmt =
  match e with
  | Id nm -> Assign (nm, assign, k)
  | Field (qual, attr) ->
      begin match UniqueMap.find attr env with
      | Some (Attribute (nm, typ)) ->
          let attr = (nm, target_type typ)
          in process_qual qual env tys (Attribute (attr, assign, []))
              (fun q -> Add (q, k))
      | _ -> failwith "attribute does not exist"
      end
  | _ -> failwith "invalid l-value expression"

(* Given a list of names and a value and type constructs a target statement
 * which extracts fields and assigns them to the given names.
 * This is used since the calculus only allows single argument functions and
 * pattern matching. *)
let rec generateVarInits (names : string list) (ty : Target.typ)
    (exp : Target.expr) (k : Target.stmt) : Target.stmt =
  match names with
  | [] -> k
  | [n] -> Assign (n, exp, k)
  | n :: ns ->
      match ty with
      | Product (x, y) ->
          Assign (n, Function (Proj (true, x, y), exp),
            generateVarInits ns y (Function (Proj (false, x, y), exp)) k)
      | _ -> failwith "Type error"


type 'a processed = Default of 'a | Set of 'a

let of_processed (x : 'a processed) : 'a = match x with Default y | Set y -> y

(* process_stmt is used to handle statements in functions/Ansible 
 * while process_module is used to handle statements in module definitions
 * which are allowed to contain variable declarations *)
(* The continuation (k) to these functions defines a statement that should come
 * at the end of the statements (such as the terminator for a loop or a return
 * for a unit-valued function). If it is not provided, reaching the end of
 * the list of statements will produce an error *)
let rec process_stmt (s : Ast.stmt list) env tys (k : Target.stmt option) : Target.stmt =
  match s with
  | [] ->
      begin match k with
      | None -> failwith "Reached end of statements, missing terminator"
      | Some s -> s
      end
  | RequiredVar _ :: _ | OptionalVar _ :: _ ->
      failwith "unexpected variable declaration"
  | ForLoop (v, l, b) :: tl ->
      process_expr l env tys
        (fun l ->
          Loop (v, l,
                process_stmt b env tys (Some (Return Env)),
                process_stmt tl env tys k))
  | IfProvided _ :: _ -> failwith "unexpected variable check"
  | IfExists (q, thn, els) :: tl ->
      let after = process_stmt tl env tys k
      in process_expr_as_elem q env tys
        (fun elem ->
          Contains (elem, process_stmt thn env tys (Some after),
                          process_stmt els env tys (Some after)))
  | IfThenElse (c, thn, els) :: tl ->
      let after = process_stmt tl env tys k
      in process_expr c env tys
          (fun c ->
            Cond (c, process_stmt thn env tys (Some after),
                     process_stmt els env tys (Some after)))
  | Match (e, cs) :: tl ->
      (* First, we need to identify the type that we are matching over. We look
       * at the first case for this *)
      begin match cs with
      | [] -> process_expr e env tys (fun _ -> process_stmt tl env tys k)
      | ((type_name, _, _), _) :: _ ->
          let after = process_stmt tl env tys k
          in let constructors = lookup_enum tys type_name
          in let cases
            = Array.make (StringMap.cardinal constructors) (Default after)
          in List.iter
              (fun ((typ, cons, vars), body) ->
                if typ <> type_name then failwith "Mismatched match cases"
                else let (pos, args) = StringMap.find cons constructors
                in match cases.(pos) with
                   | Default _ ->
                      cases.(pos) <-
                        Set (generateVarInits vars (construct_prod args)
                                (Variable "#match")
                                (process_stmt body env tys (Some after)))
                   | Set _ -> failwith "Duplicate case")
              cs
          ; process_expr e env tys
            (fun e -> Assign ("#match", e,
              array_foldr1 (Array.map of_processed cases)
                (fun l r -> Match (Variable "#match", "#match", l, r))))
      end
  | Clear e :: tl ->
      process_expr_as_qual e env tys
        (fun q -> Add (negate_qual q, process_stmt tl env tys k))
  | Assert e :: tl ->
      process_expr e env tys
        (fun e -> Cond (e, process_stmt tl env tys k, Fail "assertion failed"))
  | Return _ :: _ :: _ -> failwith "Code after return"
  | Return e :: [] -> process_expr e env tys (fun e -> Return e)
  | Assign (lhs, rhs) :: tl ->
      process_expr rhs env tys
        (fun e -> process_expr_as_lval lhs env tys e (process_stmt tl env tys k))
(* TODO *)
let process_module (_s : Ast.stmt list) _env : Target.stmt = Return Env

let codegen (files : Ast.topLevel list list) : type_env * global_env =
  (* The first step of our code generation is to divide the top levels into a
   * few groups: enums and structs; attributes, elements, and uninterpreted
   * functions; and functions and modules.
   * This order is used because we need to identify and process all types
   * before we can process definitions without bodies, and then we can finally
   * process definitions with bodies.
   *)
  let rec partition (fs : Ast.topLevel list list) =
    match fs with
    | [] -> ([], [], [])
    | [] :: fs -> partition fs
    | (t :: ts) :: fs ->
        let (tys, dfs, fns) = partition (ts :: fs) in
        match t with
        | Enum _ | Struct _ -> (t :: tys, dfs, fns)
        | Uninterp _ | Attribute _ | Element _ -> (tys, t :: dfs, fns)
        | Function _ | Module _ -> (tys, dfs, t :: fns)

  in let add_type (nm : string) (t : typ) env =
    match UniqueMap.find nm env with
    | Some (Placeholder p) -> p := Some t
    | _ -> UniqueMap.add nm t env

  in let rec create_types (ts : Ast.topLevel list) env =
    match ts with
    | [] -> ()
    | Enum (nm, variants) :: tl ->
        let variants = 
          StringMap.of_list
            (List.mapi
              (fun i (nm, ts) -> (nm, (i, create_types_option ts env)))
              variants)
        in add_type nm (Enum variants) env; create_types tl env
    | Struct (nm, fields) :: tl ->
        let fields =
          StringMap.of_list
            (List.map (fun (nm, t) -> (nm, create_type t env)) fields)
        in add_type nm (Struct fields) env; create_types tl env
    | _ :: _ -> failwith "partitioning error"

  in let rec create_definitions (ts : Ast.topLevel list) types env =
    match ts with
    | [] -> ()
    | Uninterp (nm, in_tys, out_ty) :: tl ->
        let in_typs = List.map (fun t -> process_type t types) in_tys
        and out_typ = process_type out_ty types
        in UniqueMap.add nm (Uninterpreted (nm, in_typs, out_typ)) env
        ; create_definitions tl types env
    | Attribute (nm, ty) :: tl ->
        let typ = process_type ty types
        in UniqueMap.add nm (Attribute (nm, typ)) env
        ; create_definitions tl types env
    | Element (nm, ty) :: tl ->
        let typ = process_type ty types
        in UniqueMap.add nm (Element (nm, typ)) env
        ; create_definitions tl types env
    | _ :: _ -> failwith "partitioning error"

  (* Handling functions takes two steps, we first collect type information for
   * all functions and modules and then with those definitions in hand in the
   * global environment, we actually process each function and module
   * definition *)
  in let rec create_functions (ts : Ast.topLevel list) types env =
    match ts with
    | [] -> []
    | Function (nm, args, ret, body) :: tl ->
        let arg_tys = List.map (fun (_, t) -> process_type t types) args
        and ret_ty  = process_type_option ret types
        and func_body = ref None
        in let arg_ty = construct_prod arg_tys
        in UniqueMap.add nm (Function (nm, arg_ty, ret_ty, func_body)) env
        ; (Either.Left (body, List.map fst args, arg_ty), func_body)
        :: create_functions tl types env
    | Module (nm, ret, body) :: tl ->
        let (aliases, var_types, struct_def)
          = process_module_for_args body types
        and ret_ty = process_type_option ret types
        and mod_body = ref None
        in let mod_info =
          { name = nm;
            alias_map = aliases;
            argument_types = var_types;
            input_struct_def = struct_def;
            out_type = ret_ty;
            body = mod_body }
        in add_modules nm (Module mod_info) env
        ; (Either.Right body, mod_body) :: create_functions tl types env
    | _ :: _ -> failwith "partitioning error"
  in let rec process_functions ts env types =
    match ts with
    | [] -> ()
    (* Function body *)
    | (Either.Left (body, args, arg_ty), body_ref) :: tl ->
        (* Because the calculus just has a single argument for everything we
           generate code that reads each argument out of the initial argument
           #input *)
        body_ref :=
          Some (generateVarInits args arg_ty (Variable "#input")
                    (process_stmt body env types None))
        ; process_functions tl env types
    (* Module body *)
    | (Either.Right body, body_ref) :: tl ->
        body_ref := Some(process_module body env)
        ; process_functions tl env types

  in let (tys, dfs, fns) = partition files
  in let type_env = UniqueMap.empty ()
  in let global_env : global_env = UniqueMap.empty ()
  in create_types tys type_env
  ; create_definitions dfs type_env global_env
  ; process_functions (create_functions fns type_env global_env) global_env type_env
  ; (type_env, global_env)
