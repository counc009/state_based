(* TODO: Fix error handling *)

type 'a list2 = 'a Target.list2

module IntMap    = Map.Make(Int)
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

(* Module environments reflect optional and required arguments and their state
 * so that we can determine when a variable must be provided
 * Each collection of variables is assigned a unique ID (an integer) and for
 * each collection we store whether the set of options is required and thei
 * set of variables that could be provided; we update this set as needed while
 * generating code based on the branches of if provided ... constructs *)
type mod_env = (bool * StringSet.t) IntMap.t

(* Local variables either have some name in the generated code and a type or
 * are a module argument and record their ID in the module environment along
 * with their type *)
type local_entry = LocalVar  of string * Target.typ
                 | ModuleVar of int * Target.typ
type local_env = local_entry StringMap.t

let empty_local_env : local_env = StringMap.empty
let empty_mod_env : mod_env = IntMap.empty

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

let option_some (e : Target.expr) (t : Target.typ) : Target.expr =
  Function (Constructor (false, Option t), e)

let option_none (t : Target.typ) : Target.expr =
  Function (Constructor (true, Option t), Literal (Unit ()))

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
  | Enum cs -> construct_cases cs
  | Placeholder t ->
      match !t with
      | None -> failwith "Missing type definition"
      | Some t -> target_type t
and construct_prod (ts : typ list) : Target.typ =
  match ts with
  | [] -> Primitive Unit
  | [t] -> target_type t
  | t :: ts -> Product (target_type t, construct_prod ts)
and construct_cases (cs : (int * typ list) StringMap.t) : Target.typ =
  let types : typ list array = Array.make (StringMap.cardinal cs) []
  in let ()
    = List.iter (fun (_, (i, ts)) -> types.(i) <- ts) (StringMap.to_list cs)
  in if Array.length types = 0
  then Primitive Unit
  else if Array.length types = 1
  then construct_prod types.(0)
  else Named (Cases (build_cases (Array.to_list types)))
and build_cases (cs : typ list list) : Target.typ list2 =
  match cs with
  | [] | _ :: [] -> failwith "expected at least two cases"
  | ts1 :: ts2 :: [] -> LastTwo (construct_prod ts1, construct_prod ts2)
  | ts :: cs -> Cons (construct_prod ts, build_cases cs)

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
 * - Left (named, index, typ) if nm defines a multi-constructor enum and named
 *   is the named type defining this enum, index is the constructor's index,
 *   and typ the constructor's type
 * - Right typ if nm defines a single-constructor enum, and typ is the type
 *   of the constructor
 *)
let get_enum_info (tys : type_env) (nm : string) (constr : string)
  : (Target.namedTy * int * Target.typ, Target.typ) Either.t =
  let rec extract_enum_info (t : typ)
    : (Target.namedTy * int * Target.typ, Target.typ) Either.t =
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
            | Some cs -> Either.Left (Cases cs, idx, cases.(idx))
        end
    | Option t     ->
        let typ = target_type t
        in if constr = "nothing"
        then Either.Left (Option typ, 0, Primitive Unit)
        else if constr = "some"
        then Either.Left (Option typ, 1, typ)
        else failwith "Invalid constructor of option"
    | List t       ->
        let typ = target_type t
        in if constr = "nil"
        then Either.Left (List typ, 0, Primitive Unit)
        else if constr = "cons"
        then Either.Left (List typ, 1, Product (typ, Named (List typ)))
        else failwith "Invalid constructor of list"
    | Placeholder { contents = Some t } -> extract_enum_info t
    | _ -> failwith "Not an enum type"
  in match UniqueMap.find nm tys with
  | Some t -> extract_enum_info t
  | None -> failwith "undefined type"

(* get_module_info takes the environment and an expression representing the
 * module name and returns a tuple of the information that forms the target
 * action for the module, the definition of the module's input struct, the
 * module's return type and alias map for the module's arguments
 *)
let get_module_info env (modul : Ast.expr)
  : Target.action * Target.structTy * Target.typ * string StringMap.t =
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
      in (action_info, struct_def, target_type mod_info.out_type,
          mod_info.alias_map)

(* construct_enum generates the constructors needed for an enum constructor
 * identified by the given named type and constructor index *)
let construct_enum (enum : Target.namedTy) (idx : int) (e : Target.expr)
  : Target.expr =
  let rec construct_cases (cs : Target.typ list2) (idx : int) : Target.expr =
    match cs with
    | LastTwo (_, _) ->
        if idx = 0 then Function (Constructor (true, Cases cs), e)
        else if idx = 1 then Function (Constructor (false, Cases cs), e)
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

(* construct_product_read takes a product (Target) expression, the type of that
 * expression and an index and produces and expression that reads the desired
 * index *)
let rec construct_product_read (e : Target.expr) (t : Target.typ) (i : int)
  : Target.expr * Target.typ =
  match t with
  | Product (x, y) ->
      if i = 0 then (Function (Proj (true, x, y), e), x)
      else construct_product_read (Function (Proj (false, x, y), e)) y (i - 1)
  | _ -> if i = 0 then (e, t) else failwith "not such field"

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
  ; "%" ^ string_of_int n

let fresh_var (v : string) : string =
  let n = !tmp_counter
  in tmp_counter := n + 1
  ; v ^ "." ^ string_of_int n

(* process_expr takes a continuation which takes an expression and produces a
 * statement and then returns a statement. The reason for this is that some
 * expressions in the Module language requires statmenets in the calculus and
 * so we may have to build statments as we process the expression.  This setup
 * will be placed before the statement generated by the continuation which can
 * use the result of the expression *)
let process_expr (e : Ast.expr) env tys locals (is_mod : mod_env option)
  (k : Target.expr * Target.typ -> Target.stmt) : Target.stmt =
  (* Our main helper function; it's continuation takes an "expr_result" which
   * contains at least one of an expression and a function to produce an
   * attribute; this is because of how we need to evaluate attributes. The
   * possibility of both an expression and attribute is needed to handle
   * attributes on attributes *)
  let rec process (e : Ast.expr) (k : expr_result -> Target.stmt)
    : Target.stmt =
    match e with
    | Id nm       ->
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (name, typ)) -> k (JustExpr (Variable name, typ))
        | Some _ -> failwith ("variable " ^ nm ^ " may not be provided")
        | None -> failwith "undefined variable"
        end
    | BoolLit v   -> k (JustExpr (Literal (Bool v), Primitive Bool))
    | IntLit v    -> k (JustExpr (Literal (Int v), Primitive Int))
    | FloatLit v  -> k (JustExpr (Literal (Float v), Primitive Float))
    | StringLit v -> k (JustExpr (Literal (String v), Primitive String))
    | PathLit v   -> k (JustExpr (Literal (Path v), Primitive Path))
    | UnitExp     -> k (JustExpr (Literal (Unit ()), Primitive Unit))
    | ProductExp es ->
        begin match es with
        | [] -> k (JustExpr (Literal (Unit ()), Primitive Unit))
        | [e] -> process e k
        | e :: es -> 
            process e
              (fun e ->
                match e with
                | JustExpr (e, t) | ExprOrAttr ((e, t), _)
                -> process (ProductExp es)
                  (fun es ->
                    match es with
                    | JustExpr (es, ts) | ExprOrAttr ((es, ts), _)
                    -> k (JustExpr (Pair (e, es), Product (t, ts)))
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
                            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                                if t <> StringMap.find field target_struct
                                then failwith "incorrect type for field"
                                else
                                  k (Function
                                      (AddField (target_struct, field),
                                       Pair (record, e)))
                            | _ -> failwith "expected expression"))
                    (fun e -> k (JustExpr (e, Struct target_struct)))
                    fields
                in filled_struct init_struct
            | _ -> failwith "expected struct name"
            end
        | _ -> failwith "expected struct name"
        end
    | FieldSetExp (record, field, expr) ->
        process record
          (fun r ->
            match r with
            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                begin match t with
                | Struct fields ->
                    begin match StringMap.find_opt field fields with
                    | Some ty ->
                        process expr
                          (fun a ->
                            match a with
                            | JustExpr (f, t) | ExprOrAttr ((f, t), _) ->
                                if t <> ty
                                then failwith "incorrect type for field"
                                else 
                                  k (JustExpr
                                    (Function
                                      (AddField (fields, field),
                                       Pair (e, f)),
                                     Struct fields))
                            | _ -> failwith "expected expression")
                    | None -> failwith "type does not have field"
                    end
                | _ -> failwith "type has no fields"
                end
            | _ -> failwith "expected expression")
    | EnumExp (enum, constr, args) ->
        begin match enum with
        | Id enum ->
            begin match get_enum_info tys enum constr with
            | Either.Left (enum, idx, typ) ->
                process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> typ
                        then failwith "incorrect type for constructor"
                        else
                          k (JustExpr (construct_enum enum idx e, Named enum))
                    | _ -> failwith "expected expression")
            | Either.Right typ -> process (ProductExp args)
                (fun a ->
                  match a with
                  | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                      if t <> typ
                      then failwith "incorrect type for constructor"
                      else k (JustExpr (e, t))
                  | _ -> failwith "expected expression")
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
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> snd elem
                        then failwith "incorrect type for element"
                        else 
                          k (JustAttr (fun attr -> OnElement (elem, e, attr)))
                    | _ -> failwith "expected expression")
            | Some (Uninterpreted (nm, in_tys, out_typ)) ->
                let in_ty = target_type (Product in_tys)
                and out_ty = target_type out_typ
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> in_ty
                        then failwith "incorrect type for uninterpreted function"
                        else 
                          k (JustExpr (
                              Function (Uninterpreted (nm, in_ty, out_ty), e),
                              out_ty))
                    | _ -> failwith "expected expression")
            | Some (Function (nm, arg_typ, ret_typ, body)) ->
                (* Function calls are translated into statements because
                 * functions actually become actions in the calculus *)
                let ret_ty = target_type ret_typ
                and tmp = temp_name ()
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> arg_typ
                        then failwith "incorrect type for function"
                        else
                          Action (tmp, (nm, arg_typ, ret_ty, body), e,
                                  k (JustExpr (Variable tmp, ret_ty)))
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
                      | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                          if t <> snd elem
                          then failwith "incorrect type on element"
                          else 
                            k (JustAttr (fun attr 
                              -> qual (OnElement (elem, e, attr))))
                      | _ -> failwith "expected expression")
                    | JustExpr _ -> failwith "expected element")
            | Some _ -> failwith "expected element"
            | None -> failwith "undefined name"
            end
        | _ -> failwith "invalid function expression"
        end
      | ModuleExp (func, args) ->
          let (mod_info, record_def, ret_ty, aliases) 
            = get_module_info env func
          and tmp = temp_name ()
          in let init_input : Target.expr =
            Function (EmptyStruct record_def, Literal (Unit ()))
          in let assigned_args : Ast.expr StringMap.t =
            List.fold_left
              (fun (args : Ast.expr StringMap.t) (field, expr) ->
                let canonical =
                  match StringMap.find_opt field aliases with
                  | Some nm -> nm
                  | None -> field
                in if not (StringMap.mem canonical record_def)
                then failwith ("unexpected argument " ^ canonical)
                else StringMap.update canonical
                  (fun v ->
                    match v with
                    | Some _ -> failwith ("multiple values for argument "
                                          ^ canonical)
                    | None -> Some expr) args)
              StringMap.empty
              args
          in let filled_args : Target.expr -> Target.stmt =
            StringMap.fold
              (fun field ty (k : Target.expr -> Target.stmt) record ->
                match StringMap.find_opt field assigned_args with
                | Some e ->
                    process e
                    (fun field_expr ->
                      match field_expr with
                      | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                          if t <> ty
                          then failwith "incorrect module argument type"
                          else
                            k (Function
                                (AddField (record_def, field),
                                Pair (record, option_some e ty)))
                      | _ -> failwith "expected expression")
                | None ->
                    k (Function (AddField (record_def, field),
                                 Pair (record, option_none ty))))
              record_def
              (fun e ->
                Action (tmp, mod_info, e,
                        k (JustExpr (Variable tmp, ret_ty))))
          in filled_args init_input
    | Field (lhs, field) ->
        process lhs
          (fun e ->
            match e with
            | JustExpr (e, t) ->
                begin match t with
                | Struct fields ->
                    begin match StringMap.find_opt field fields with
                    | Some ty -> 
                        k (JustExpr
                            (Function (ReadField (fields, field), e),
                             ty))
                    | None -> failwith "invalid field"
                    end
                | _ -> failwith "does not have fields"
                end
            | JustAttr qual ->
                begin match UniqueMap.find field env with
                | Some (Attribute (nm, typ)) ->
                    let attr = (nm, target_type typ)
                    and tmp = temp_name ()
                    in Get (tmp, qual (AttrAccess attr),
                        k (ExprOrAttr (
                              (Variable tmp, snd attr),
                              fun a -> qual (OnAttribute (attr, a)))))
                | Some _ -> failwith "expected attribute"
                | None -> failwith "undefined attribute"
                end
            | ExprOrAttr ((e, t), qual) ->
                (* If the left-hand side can either be an expression or an
                 * attribute (say because it is an attribute access) we check
                 * whether this field exists as an attribute and whether it
                 * exists on the expression. If it exists on both, fail.
                 * TODO: We should report a warning but treat this as an
                 * attribute access *)
                match UniqueMap.find field env with
                | Some (Attribute (nm, typ)) ->
                    (* Check whether the expression interpretation has this as
                     * a field *)
                    if match t with
                       | Struct fields -> StringMap.mem field fields
                       | _ -> false
                    then 
                      failwith "field is either a struct field or an attribute"
                    else
                      let attr = (nm, target_type typ)
                      and tmp = temp_name ()
                      in Get (tmp, qual (AttrAccess attr),
                          k (ExprOrAttr (
                                (Variable tmp, snd attr),
                                fun a -> qual (OnAttribute (attr, a)))))
                | _ ->
                    (* Read a field from a struct *)
                    match t with
                    | Struct fields ->
                        begin match StringMap.find_opt field fields with
                        | Some ty ->
                            k (JustExpr
                                (Function (ReadField (fields, field), e),
                                 ty))
                        | None -> failwith "invalid field"
                        end
                    | _ -> failwith "does not have fields")
    | ProductField (lhs, idx) ->
        process lhs
          (fun e ->
            match e with
            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                let (res, res_ty) = construct_product_read e t idx
                in k (JustExpr (res, res_ty))
            | _ -> failwith "expected expression")
    | UnaryExp (_, _) -> failwith "TODO"
    | BinaryExp (_, _, _) -> failwith "TODO"
    | CondExp (cond, thn, els) ->
        process cond
          (fun e ->
            match e with
            | JustExpr (c, t) | ExprOrAttr ((c, t), _) ->
                if t <> Primitive Bool
                then failwith "non-boolean condition"
                else
                  let tmp = temp_name ()
                  in process thn (fun lhs ->
                      process els (fun rhs ->
                      let (thn, thn_t) =
                        match lhs with
                        | JustExpr (thn, thn_t) | ExprOrAttr ((thn, thn_t), _)
                          -> (thn, thn_t)
                        | _ -> failwith "expected expression"
                      and (els, els_t) =
                        match rhs with
                        | JustExpr (els, els_t) | ExprOrAttr ((els, els_t), _)
                          -> (els, els_t)
                        | _ -> failwith "expected expression"
                      in if thn_t <> els_t
                      then failwith "types of ternary branches do not match"
                      else
                        let after = k (JustExpr (Variable tmp, thn_t))
                        in Cond (c, Assign (tmp, thn, after),
                                    Assign (tmp, els, after))))
            | _ -> failwith "expected expression")
    | CondProvidedExp (_var, _thn, _els) ->
        begin match is_mod with
        | None -> failwith "unexpected variable check"
        | Some _mod_env -> failwith "TODO"
        end
  in process e
    (fun e -> match e with
              | JustExpr (e, t) | ExprOrAttr ((e, t), _) -> k (e, t)
              | JustAttr _ -> failwith "Expected expression, not element")

let rec process_qual (e : Ast.expr) env tys locals (is_mod : mod_env option)
  (q : Target.qual) (k : Target.qual -> Target.stmt) : Target.stmt =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then failwith "incorrect type in element"
                else k (Element (elem, expr, [q])))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then failwith "incorrect type in element"
              else process_qual qual env tys locals is_mod
                                (Element (elem, expr, [q])) k)
      | _ -> failwith "Invalid element"
      end
  | Field (qual, attr) ->
      begin match UniqueMap.find attr env with
      | Some (Attribute (nm, typ)) ->
          let attr = (nm, target_type typ)
          (* By processing the current expression we produce the current value
           * of the attribute *)
          in process_expr e env tys locals is_mod
            (fun (expr, _) ->
              process_qual qual env tys locals is_mod 
                           (Attribute (attr, expr, [q])) k)
      | _ -> failwith "Invalid attribute"
      end
  | _ -> failwith "Invalid qualifier"

(* Process an expression for a clear statement (the final access is not an
   attribute) *)
let process_expr_as_qual (e : Ast.expr) env tys locals
  (is_mod : mod_env option) (k : Target.qual -> Target.stmt) : Target.stmt =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then failwith "incorrect type on element"
                else k (Element (elem, expr, [])))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then failwith "incorrect type on element"
              else process_qual qual env tys locals is_mod
                                (Element (elem, expr, [])) k)
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

let process_expr_as_elem (e : Ast.expr) env tys locals
  (is_mod : mod_env option) (k : Target.elem -> Target.stmt) : Target.stmt =
  let rec process_elem (q : Ast.expr) (e : Target.elem)
    (k : Target.elem -> Target.stmt) : Target.stmt =
    match q with
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
                (fun (expr, typ) ->
                  if typ <> snd elem
                  then failwith "incorrect type on element"
                  else k (OnElement (elem, expr, e)))
        | _ -> failwith "Invalid element"
        end
    | FuncExp (Field (qual, elem), args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then failwith "incorrect type on element"
                else process_elem qual (OnElement (elem, expr, e)) k)
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
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then failwith "incorrect type on element"
                else k (Element (elem, expr)))
      | _ -> failwith "Invalid element"
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then failwith "incorrect type on element"
              else process_elem qual (Element (elem, expr)) k)
      | _ -> failwith "Invalid element"
      end
  | _ -> failwith "Invalid qualifier"

(* As we process l-values we either have have a value (such as a variable or a
 * field access) or we have an attribute *)
type lval_res =
  (* For values we return the type of the value, an expression which evaluates
   * its current value, and a continuation which builds the assignment to that
   * value for a given expression being assigned and statement to follow *)
  | LValue     of Target.typ * Target.expr
                * (Target.expr -> Target.stmt -> Target.stmt)
  (* For attributes, we return both the attribute as a qualifier with other
   * elements/attributes following it and as the top-level attribute (which is
   * a continuation expecting the value being assigned) *)
  | LAttribute of ((Target.qual -> Target.qual) * (Target.attr -> Target.attr))
                * (Target.typ * Target.expr * (Target.expr -> Target.qual))
  | LElement   of (Target.qual -> Target.qual) * (Target.attr -> Target.attr)

let process_lval (e : Ast.expr) env tys locals (is_mod : mod_env option)
  (assigned : Target.expr) (typ : Target.typ) (k : Target.stmt) : Target.stmt =
  let rec process (e : Ast.expr) (k : lval_res -> Target.stmt) : Target.stmt =
    match e with
    | Id nm ->
        (* Attributes are not supported on the top-level of the state, so an
         * identifier must be a local variable *)
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (var, typ)) ->
            k (LValue (typ, Variable var, fun e s -> Assign (var, e, s)))
        | Some _ -> failwith ("variable " ^ nm ^ " may not be provided")
        | None -> failwith ("undefined variable " ^ nm)
        end
    | Field (lhs, field) ->
        process lhs
          (fun res ->
            match res with
            | LValue (typ, exp, assign) ->
                begin match typ with
                | Struct fields ->
                    begin match StringMap.find_opt field fields with
                    | Some ty ->
                        k (LValue (ty, Function (ReadField (fields, field), exp),
                          fun e s ->
                            assign 
                              (Function
                                (AddField (fields, field),
                                 Pair (exp, e)))
                              s))
                    | None -> failwith ("does not have field " ^ field)
                    end
                | _ -> failwith "has no fields"
                end
            | LAttribute ((as_qual, as_attr), (typ, expr, as_assign)) ->
                let is_field =
                  match typ with
                  | Struct fields ->
                      begin match StringMap.find_opt field fields with
                      | Some ty -> Some (fields, ty)
                      | _ -> None
                      end
                  | _ -> None
                and is_attr =
                  match UniqueMap.find field env with
                  | Some (Attribute (nm, typ)) -> Some (nm, target_type typ)
                  | _ -> None
                in begin match is_field, is_attr with
                | Some _, Some _ -> failwith "ambiguous field or attribute"
                | None, None -> failwith "undefined field or attribute"
                | Some (fields, field_ty), None ->
                    k (LValue (field_ty, 
                               Function (ReadField (fields, field), expr),
                               fun e s -> Add (as_assign e, s)))
                | None, Some attr ->
                    let tmp = temp_name ()
                    in Get (tmp, as_attr (AttrAccess attr),
                    k (LAttribute (
                        ((fun q
                          -> as_qual (Attribute (attr, Variable tmp, [q]))),
                         (fun a
                          -> as_attr (OnAttribute (attr, a)))),
                        (snd attr, Variable tmp,
                         fun e -> as_qual (Attribute (attr, e, []))))))
                end
            | LElement (as_qual, as_attr) ->
                match UniqueMap.find field env with
                | Some (Attribute (nm, typ)) ->
                    let attr = (nm, target_type typ)
                    and tmp = temp_name ()
                    in Get (tmp, as_attr (AttrAccess attr),
                    k (LAttribute (
                        ((fun q
                          -> as_qual (Attribute (attr, Variable tmp, [q]))),
                         (fun a
                          -> as_attr (OnAttribute (attr, a)))),
                        (snd attr, Variable tmp,
                         fun e -> as_qual (Attribute (attr, e, []))))))
                | _ -> failwith "expected attribute")
    | ProductField (_lhs, _idx) -> failwith "TODO"
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
              (fun (e, t) ->
                if t <> snd elem
                then failwith ("incorrect type for element " ^ nm)
                else Add (Element (elem, e, []),
                  k (LElement ((fun q -> Element (elem, e, [q])),
                                  (fun a -> OnElement (elem, e, a))))))
        | Some _ -> failwith "expected element"
        | _ -> failwith ("undefined name " ^ elem)
        end
    | FuncExp (Field (lhs, elem), args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process lhs
            (fun res ->
              match res with
              | LValue (_, _, _) -> failwith "cannot access element on value"
              | LAttribute ((as_qual, as_attr), _)
              | LElement   (as_qual, as_attr) ->
                  process_expr (ProductExp args) env tys locals is_mod
                  (fun (e, t) ->
                    if t <> snd elem
                    then failwith ("incorrect type for element " ^ nm)
                    else Add (as_qual (Element (elem, e, [])),
                      k (LElement (
                            (fun q -> as_qual (Element (elem, e, [q]))),
                            (fun a -> as_attr (OnElement (elem, e, a))))))))
        | Some _ -> failwith "expected element"
        | _ -> failwith ("undefined name " ^ elem)
        end
    | _ -> failwith "invalid l-value"
  in process e
    (fun res ->
      match res with
      | LValue (t, _, assign) ->
          if t <> typ
          then failwith "incorrect type in assignment"
          else assign assigned k
      | LAttribute (_, (t, _, attr)) ->
          if t <> typ
          then failwith "incorrect type in assignment"
          else Add (attr assigned, k)
      | LElement _ -> failwith "expected l-value, found element")

(* Given a list of names and a value and type constructs a target statement
 * which extracts fields and assigns them to the given names.
 * This is used since the calculus only allows single argument functions and
 * pattern matching. *)
let rec generateVarInits (names : string list) (ty : Target.typ)
    (exp : Target.expr) (locals : local_env) (k : local_env -> Target.stmt)
    : Target.stmt =
  match names with
  | [] -> k locals
  | [n] ->
      let fresh_n = fresh_var n
      in Assign (fresh_n, exp,
                  k (StringMap.add n (LocalVar (fresh_n, ty)) locals))
  | n :: ns ->
      match ty with
      | Product (x, y) ->
          let fresh_n = fresh_var n
          in Assign (fresh_n, Function (Proj (true, x, y), exp),
            generateVarInits ns y (Function (Proj (false, x, y), exp))
              (StringMap.add n (LocalVar (fresh_n, x)) locals) k)
      | _ -> failwith "Type error"


type 'a processed = Default of 'a | Set of 'a

let of_processed (x : 'a processed) : 'a = match x with Default y | Set y -> y

(* process_stmt's is_mod argument specifies whether variable declarations
 * and checks are allowed in the code or not, so this function can be used to
 * generate code for both functions and modules. *)
(* The continuation (k) to these functions defines a statement that should come
 * at the end of the statements (such as the terminator for a loop or a return
 * for a unit-valued function). If it is not provided, reaching the end of
 * the list of statements will produce an error *)
let rec process_stmt (s : Ast.stmt list) env tys locals
  (is_mod : mod_env option) (k : Target.stmt option) : Target.stmt =
  match s with
  | [] ->
      begin match k with
      | None -> failwith "Reached end of statements, missing terminator"
      | Some s -> s
      end
  | RequiredVar _ :: _ | OptionalVar _ :: _ ->
      begin match is_mod with
      | None -> failwith "unexpected variable check"
      | Some _mod_env -> failwith "TODO"
      end
  | ForLoop (v, l, b) :: tl ->
      process_expr l env tys locals is_mod
        (fun (lst, typ) ->
          match typ with
          | Named (List t) ->
            let fresh_v = fresh_var v
            in let body_env = StringMap.add v (LocalVar (fresh_v, t)) locals
            in
            Loop (fresh_v, lst,
                  process_stmt b env tys body_env is_mod (Some (Return Env)),
                  process_stmt tl env tys locals is_mod k)
          | _ -> failwith "can only loop over lists")
  | IfProvided _ :: _ ->
      begin match is_mod with
      | None -> failwith "unexpected variable check"
      | Some _mod_env -> failwith "TODO"
      end
  | IfExists (q, thn, els) :: tl ->
      let after = process_stmt tl env tys locals is_mod k
      in process_expr_as_elem q env tys locals is_mod
        (fun elem ->
          Contains (elem, process_stmt thn env tys locals is_mod (Some after),
                          process_stmt els env tys locals is_mod (Some after)))
  | IfThenElse (c, thn, els) :: tl ->
      let after = process_stmt tl env tys locals is_mod k
      in process_expr c env tys locals is_mod
          (fun (c, _) ->
            Cond (c, process_stmt thn env tys locals is_mod (Some after),
                     process_stmt els env tys locals is_mod (Some after)))
  | Match (e, cs) :: tl ->
      (* First, we need to identify the type that we are matching over. We look
       * at the first case for this *)
      begin match cs with
      | [] ->
          process_expr e env tys locals is_mod
            (fun _ -> process_stmt tl env tys locals is_mod k)
      | ((type_name, _, _), _) :: _ ->
          let after = process_stmt tl env tys locals is_mod k
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
                                  process_stmt body env tys locals is_mod
                                               (Some after)))
                   | Set _ -> failwith "Duplicate case")
              cs
          ; process_expr e env tys locals is_mod
            (fun (e, _) -> Assign ("#match", e,
              array_foldr1 (Array.map of_processed cases)
                (fun l r -> Match (Variable "#match", "#match", l, r))))
      end
  | Clear e :: tl ->
      process_expr_as_qual e env tys locals is_mod
        (fun q -> Add (negate_qual q, process_stmt tl env tys locals is_mod k))
  | Assert e :: tl ->
      process_expr e env tys locals is_mod
        (fun (e, _) ->
          Cond (e, process_stmt tl env tys locals is_mod k,
                   Fail "assertion failed"))
  | AssertExists q :: tl ->
      process_expr_as_elem q env tys locals is_mod
        (fun elem ->
          Contains (elem, process_stmt tl env tys locals is_mod k,
                    Fail "assertion failed"))
  | Return _ :: _ :: _ -> failwith "Code after return"
  | Return e :: [] ->
      process_expr e env tys locals is_mod (fun (e, _) -> Return e)
  | LetStmt (var, exp) :: tl ->
      process_expr exp env tys locals is_mod
        (fun (e, t) ->
          let fresh_var = fresh_var var
          in let locals = StringMap.add var (LocalVar (fresh_var, t)) locals
          in Assign (fresh_var, e, process_stmt tl env tys locals is_mod k))
  | Assign (lhs, rhs) :: tl ->
      (* Assign statements do not create new bindings (lets do that) and so
       * everything can be evaluated under the same local environment *)
      process_expr rhs env tys locals is_mod
        (fun (e, t) ->
          process_lval lhs env tys locals is_mod e t
            (process_stmt tl env tys locals is_mod k))

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
        | Enum _ | Struct _ | Type _ -> (t :: tys, dfs, fns)
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
    | Type (nm, typ) :: tl ->
        let ty = create_type typ env
        in add_type nm ty env; create_types tl env
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
                (fun locals -> 
                  process_stmt body env types locals None default_ret))
        ; process_functions tl env types
    (* Module body *)
    | (Either.Right body, ret_type, body_ref) :: tl ->
        let default_ret : Target.stmt option =
          if type_equality ret_type Unit
          then Some (Return (Literal (Unit ())))
          else None
        in
        body_ref := 
          Some(process_stmt body env types empty_local_env
                (Some empty_mod_env) default_ret)
        ; process_functions tl env types

  in let (tys, dfs, fns) = partition files
  in let type_env = UniqueMap.empty ()
  in let global_env : global_env = UniqueMap.empty ()
  in create_types tys type_env
  ; create_definitions dfs type_env global_env
  ; process_functions (create_functions fns type_env global_env) global_env type_env
  ; (type_env, global_env)

let codegen_program (body : Ast.stmt list) tys env : Target.stmt =
  process_stmt body env tys empty_local_env None
    (Some (Return (Literal (Unit ()))))
