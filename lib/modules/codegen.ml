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

type local_env = Target.typ StringMap.t

let empty_local_env : local_env = StringMap.empty

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

(* get_module_info takes the environment and an expression representing the
 * module name and returns a tuple of the information that forms the target
 * action for the module, the definition of the module's input struct, and
 * alias map for the module's arguments
 *)
let get_module_info env (modul : Ast.expr)
  : Target.action * Target.structTy * string StringMap.t =
  let rec find_module env (modul : Ast.expr)
    : (global_env, module_info) Either.t =
    match modul with
    | Id nm ->
        begin match UniqueMap.find nm env with
        | Some (Module mod_info) -> Either.Right mod_info
        | Some (Environment env) -> Either.Left env
        | Some _ -> failwith "expected module"
        | None -> failwith "undefined name"
        end
    | Field (modul, nm) ->
        begin match find_module env modul with
        | Either.Right _ -> failwith "no such field"
        | Either.Left env ->
            match UniqueMap.find nm env with
            | Some (Module mod_info) -> Either.Right mod_info
            | Some (Environment env) -> Either.Left env
            | Some _ -> failwith "expected module"
            | None -> failwith "undefined name"
        end
    | _ -> failwith "expected module name"
  in match find_module env modul with
  | Either.Left _ -> failwith "expected module name"
  | Either.Right mod_info ->
      let struct_def = StringMap.map target_type mod_info.input_struct_def
      in let action_info : Target.action = 
        (String.concat "." mod_info.name,
         Struct struct_def,
         target_type mod_info.out_type,
         mod_info.body)
      in (action_info, struct_def, mod_info.alias_map)

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
type expr_result = JustExpr of Target.expr * Target.typ
                 | JustAttr of (Target.attr -> Target.attr)
                 | ExprOrAttr of (Target.expr * Target.typ) 
                               * (Target.attr -> Target.attr)

(* Generation of unique temporary names *)
let tmp_counter : int ref = ref 0

let temp_name () : string =
  let n = !tmp_counter
  in tmp_counter := n + 1
  ; "#" ^ string_of_int n

(* TODO *)
(* process_expr takes a continuation which takes an expression and produces a
 * statement and then returns a statement. The reason for this is that some
 * expressions in the Module language requires statmenets in the calculus and
 * so we may have to build statments as we process the expression.  This setup
 * will be placed before the statement generated by the continuation which can
 * use the result of the expression *)
let process_expr (e : Ast.expr) _env _tys _locals
  (k : Target.expr * Target.typ -> Target.stmt) : Target.stmt =
  (* Our main helper function; it's continuation takes an "expr_result" which
   * contains at least one of an expression and a function to produce an
   * attribute; this is because of how we need to evaluate attributes. The
   * possibility of both an expression and attribute is needed to handle
   * attributes on attributes *)
  let (*rec*) process (_e : Ast.expr) (_k : expr_result -> Target.stmt)
    : Target.stmt =
      failwith "FIXME"
    (* FIXME *)
    (*
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
        | Id nm ->
            begin match UniqueMap.find nm env with
            | Some (Element (nm, tys)) ->
                let elem = (nm, target_type tys)
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr e | ExprOrAttr (e, _) ->
                        k (JustAttr (fun attr -> OnElement (elem, e, attr)))
                    | _ -> failwith "expected expression")
            | Some (Uninterpreted (nm, in_tys, out_typ)) ->
                let in_ty = target_type (Product in_tys)
                and out_ty = target_type out_typ
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr e | ExprOrAttr (e, _) ->
                        k (JustExpr 
                          (Function (Uninterpreted (nm, in_ty, out_ty), e)))
                    | _ -> failwith "expected expression")
            | Some (Function (nm, arg_typ, ret_typ, body)) ->
                (* Function calls are translated into statements because
                 * functions actually become actions in the calculus *)
                let ret_ty = target_type ret_typ
                and tmp = temp_name ()
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr e | ExprOrAttr (e, _) ->
                        Action (tmp, (nm, arg_typ, ret_ty, body), e,
                                k (JustExpr (Variable tmp)))
                    | _ -> failwith "expected expression")
            | Some _ -> failwith "expected function"
            | None -> failwith "undefined name"
            end
        | Field (qual, nm) ->
            begin match UniqueMap.find nm env with
            | Some (Element (nm, tys)) ->
                let elem = (nm, target_type tys)
                in process qual
                  (fun q ->
                    match q with
                    | JustAttr qual | ExprOrAttr (_, qual)
                    -> process (ProductExp args)
                    (fun a ->
                      match a with
                      | JustExpr e | ExprOrAttr (e, _) ->
                          k (JustAttr 
                            (fun attr -> qual (OnElement (elem, e, attr))))
                      | _ -> failwith "expected expression")
                    | JustExpr _ -> failwith "expected element")
            | Some _ -> failwith "expected element"
            | None -> failwith "undefined name"
            end
        | ModuleExp (func, args) ->
            let (mod_info, record_def, aliases) = get_module_info env func
            and tmp = temp_name ()
            in let init_input : Target.expr =
              Function (EmptyStruct record_def, Literal (Unit ()))
            in let filled_args : Target.expr -> Target.stmt =
              List.fold_left
                (fun (k : Target.expr -> Target.stmt) (field, expr) record ->
                  let canonical =
                    match StringMap.find_opt field aliases with
                    | Some nm -> nm
                    | None -> field
                  in if not (StringMap.mem canonical record_def)
                  then failwith "unexpected argument"
                  else
                    process expr
                      (fun field_expr ->
                        match field_expr with
                        | JustExpr e | ExprOrAttr (e, _) ->
                            k (Function (AddField (record_def, canonical),
                                Pair (record, e)))
                        | _ -> failwith "expected expression"))
              (fun e -> Action (tmp, mod_info, e, k (JustExpr (Variable tmp))))
              args
            in filled_args init_input
        | _ -> failwith "invalid function expression"
        end
    | _ -> failwith "TODO"
    *)
  in process e
    (fun e -> match e with
              | JustExpr (e, t) | ExprOrAttr ((e, t), _) -> k (e, t)
              | JustAttr _ -> failwith "Expected expression, not element")

(* FIXME *)
let (*rec*) process_qual (_e : Ast.expr) _env _tys _locals (_q : Target.qual)
  (_k : Target.qual -> Target.stmt) : Target.stmt =
    failwith "FIXME"
  (*
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
  *)

(* Process an expression for a clear statement (the final access is not an
   attribute) *)
let process_expr_as_qual (_e : Ast.expr) _env _tys _locals
  (_k : Target.qual -> Target.stmt) : Target.stmt =
    failwith "FIXME"
  (*
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
  *)

let rec negate_qual (q : Target.qual) : Target.qual =
  match q with
  | Attribute (_, _, []) -> failwith "Cannot negate an attribute"
  | Attribute (a, e, qs) -> Attribute (a, e, List.map negate_qual qs)
  | Element (e, ex, []) -> NotElement (e, ex)
  | Element (e, ex, qs) -> Element (e, ex, List.map negate_qual qs)
  | NotElement (_, _) -> failwith "Cannot generate negated qual from front-end"

let process_expr_as_elem (_e : Ast.expr) _env _tys _locals
  (_k : Target.elem -> Target.stmt) : Target.stmt =
    failwith "FIXME"
  (*
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
  *)

(* L-values are only variables and attributes in the state *)
let process_lval_as_qual (e : Ast.expr) env tys locals
  (assign : Target.expr * Target.typ) (k : Target.stmt) : Target.stmt =
  match e with
  | Field (qual, attr) ->
      begin match UniqueMap.find attr env with
      | Some (Attribute (nm, typ)) ->
          let attr = (nm, target_type typ)
          in if snd attr != snd assign
          then failwith "invalid type in attribute assignment"
          else process_qual qual env tys locals
                  (Attribute (attr, fst assign, []))
                  (fun q -> Add (q, k))
      | _ -> failwith "attribute does not exist"
      end
  | _ -> failwith "invalid l-value expression"

(* Given a list of names and a value and type constructs a target statement
 * which extracts fields and assigns them to the given names.
 * This is used since the calculus only allows single argument functions and
 * pattern matching. *)
let rec generateVarInits (names : string list) (ty : Target.typ)
    (exp : Target.expr) (locals : local_env) (k : local_env -> Target.stmt)
    : Target.stmt =
  match names with
  | [] -> k locals
  | [n] -> Assign (n, exp, k (StringMap.add n ty locals))
  | n :: ns ->
      match ty with
      | Product (x, y) ->
          Assign (n, Function (Proj (true, x, y), exp),
            generateVarInits ns y (Function (Proj (false, x, y), exp))
              (StringMap.add n x locals) k)
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
let rec process_stmt (s : Ast.stmt list) env tys locals
  (k : Target.stmt option) : Target.stmt =
  match s with
  | [] ->
      begin match k with
      | None -> failwith "Reached end of statements, missing terminator"
      | Some s -> s
      end
  | RequiredVar _ :: _ | OptionalVar _ :: _ ->
      failwith "unexpected variable declaration"
  | ForLoop (v, l, b) :: tl ->
      process_expr l env tys locals
        (fun l ->
          let body_env = StringMap.add v (snd l) locals
          in
          Loop (v, fst l,
                process_stmt b env tys body_env (Some (Return Env)),
                process_stmt tl env tys locals k))
  | IfProvided _ :: _ -> failwith "unexpected variable check"
  | IfExists (q, thn, els) :: tl ->
      let after = process_stmt tl env tys locals k
      in process_expr_as_elem q env tys locals
        (fun elem ->
          Contains (elem, process_stmt thn env tys locals (Some after),
                          process_stmt els env tys locals (Some after)))
  | IfThenElse (c, thn, els) :: tl ->
      let after = process_stmt tl env tys locals k
      in process_expr c env tys locals
          (fun (c, _) ->
            Cond (c, process_stmt thn env tys locals (Some after),
                     process_stmt els env tys locals (Some after)))
  | Match (e, cs) :: tl ->
      (* First, we need to identify the type that we are matching over. We look
       * at the first case for this *)
      begin match cs with
      | [] ->
          process_expr e env tys locals
            (fun _ -> process_stmt tl env tys locals k)
      | ((type_name, _, _), _) :: _ ->
          let after = process_stmt tl env tys locals k
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
                                (Variable "#match") locals
                                (fun locals -> 
                                  process_stmt body env tys locals 
                                    (Some after)))
                   | Set _ -> failwith "Duplicate case")
              cs
          ; process_expr e env tys locals
            (fun (e, _) -> Assign ("#match", e,
              array_foldr1 (Array.map of_processed cases)
                (fun l r -> Match (Variable "#match", "#match", l, r))))
      end
  | Clear e :: tl ->
      process_expr_as_qual e env tys locals
        (fun q -> Add (negate_qual q, process_stmt tl env tys locals k))
  | Assert e :: tl ->
      process_expr e env tys locals
        (fun (e, _) ->
          Cond (e, process_stmt tl env tys locals k, Fail "assertion failed"))
  | Return _ :: _ :: _ -> failwith "Code after return"
  | Return e :: [] -> process_expr e env tys locals (fun (e, _) -> Return e)
  | Assign (lhs, rhs) :: tl ->
      match lhs with
      | Id nm ->
          process_expr rhs env tys locals
            (fun (e, t) ->
              let locals = StringMap.add nm t locals
              in Assign (nm, e, process_stmt tl env tys locals k))
      | _ ->
          process_expr rhs env tys locals
            (fun e ->
              process_lval_as_qual lhs env tys locals e
                (process_stmt tl env tys locals k))
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
        ; (Either.Left (body, List.map fst args, arg_ty), ret_ty, func_body)
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
        ; (Either.Right body, ret_ty, mod_body)
        :: create_functions tl types env
    | _ :: _ -> failwith "partitioning error"
  in let rec process_functions ts env types =
    match ts with
    | [] -> ()
    (* Function body *)
    | (Either.Left (body, args, arg_ty), ret_type, body_ref) :: tl ->
        (* Because the calculus just has a single argument for everything we
           generate code that reads each argument out of the initial argument
           #input *)
        let default_ret : Target.stmt option =
          if type_equality ret_type Unit
          then Some (Return (Literal (Unit ())))
          else None
        in
        body_ref :=
          Some 
            (generateVarInits args arg_ty (Variable "#input")
                empty_local_env
                (fun locals -> process_stmt body env types locals default_ret))
        ; process_functions tl env types
    (* Module body *)
    | (Either.Right body, _ret_type, body_ref) :: tl ->
        body_ref := Some(process_module body env)
        ; process_functions tl env types

  in let (tys, dfs, fns) = partition files
  in let type_env = UniqueMap.empty ()
  in let global_env : global_env = UniqueMap.empty ()
  in create_types tys type_env
  ; create_definitions dfs type_env global_env
  ; process_functions (create_functions fns type_env global_env) global_env type_env
  ; (type_env, global_env)
