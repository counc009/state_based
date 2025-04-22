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

let unwrap (x: ('a, string) result) : 'a =
  match x with
  | Ok y -> y
  | Error msg -> failwith ("Error: " ^ msg)

type 'a placeholder = 'a option ref

type typ = Bool | Int | Float | String | Path | Unit
         | Option      of typ
         | List        of typ
         | Product     of typ list
         | Struct      of typ StringMap.t
         (* Store the name of the enum along with the info on its constructors *)
         | Enum        of string * (int * typ list) StringMap.t
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
    args : Ast.typ StringMap.t;
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
(* The module info we store also records the input type of the module *)
type mod_info = mod_env * Target.typ StringMap.t

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
  | Enum (_, res) -> res
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
  : string StringMap.t * Ast.typ StringMap.t * typ StringMap.t * typ StringMap.t = 
  let rec add_alias alias nm aliases =
    match alias with
    | [] -> aliases
    | v :: tl ->
        match StringMap.find_opt v aliases with
        | None -> add_alias tl nm (StringMap.add v nm aliases)
        | Some n ->
            if n = nm then add_alias tl nm aliases
            else failwith "variable already used as alias with different canonical name"
  in let rec add_vars vars aliases ast_types var_types struct_def =
    match vars with
    | [] -> (aliases, ast_types, var_types, struct_def)
    | (nm, alias, typ, _) :: tl ->
        let ast_types = StringMap.add nm typ ast_types
        in let typ = process_type typ env
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
        in add_vars tl aliases ast_types var_types struct_def
  in let rec process (body : Ast.stmt list) aliases ast_types var_types struct_def =
    match body with
    | [] -> (aliases, ast_types, var_types, struct_def)
    | VarDecls (_, vars) :: tl ->
        let (aliases, ast_types, var_types, struct_def)
          = add_vars vars aliases ast_types var_types struct_def
        in process tl aliases ast_types var_types struct_def
    | ForLoop (_, _, body) :: tl ->
        let (aliases, ast_types, var_types, struct_def)
          = process body aliases ast_types var_types struct_def
        in process tl aliases ast_types var_types struct_def
    | IfProvided (_, thn, els) :: tl | IfThenElse (_, thn, els) :: tl ->
        let (aliases, ast_types, var_types, struct_def)
          = process thn aliases ast_types var_types struct_def
        in let (aliases, ast_types, var_types, struct_def)
          = process els aliases ast_types var_types struct_def
        in process tl aliases ast_types var_types struct_def
    | Match (_, cases) :: tl ->
        List.fold_left
          (fun (aliases, ast_types, var_types, struct_def) (_, case)
            -> process case aliases ast_types var_types struct_def)
          (process tl aliases ast_types var_types struct_def)
          cases
    | _ :: tl -> process tl aliases ast_types var_types struct_def
  in process body StringMap.empty StringMap.empty StringMap.empty StringMap.empty

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
  | Enum (nm, cs) -> construct_cases nm cs
  | Placeholder t ->
      match !t with
      | None -> failwith "Missing type definition"
      | Some t -> target_type t
and construct_prod (ts : typ list) : Target.typ =
  match ts with
  | [] -> Primitive Unit
  | [t] -> target_type t
  | t :: ts -> Product (target_type t, construct_prod ts)
and construct_cases (enum_name : string) (cs : (int * typ list) StringMap.t)
  : Target.typ =
  let types : (string * typ list) array 
    = Array.make (StringMap.cardinal cs) ("", [])
  in let ()
    = List.iter
        (fun (nm, (i, ts)) -> types.(i) <- (nm, ts))
        (StringMap.to_list cs)
  in if Array.length types = 0
  then Primitive Unit
  else if Array.length types = 1
  then construct_prod (snd types.(0))
  else Named (Cases (enum_name, build_cases (Array.to_list types)))
and build_cases (cs : (string * typ list) list) : (string * Target.typ) list2 =
  match cs with
  | [] | _ :: [] -> failwith "expected at least two cases"
  | (nm1, ts1) :: (nm2, ts2) :: [] ->
      LastTwo ((nm1, construct_prod ts1), (nm2, construct_prod ts2))
  | (nm, ts) :: cs -> Cons ((nm, construct_prod ts), build_cases cs)

let rec to_list2 (xs : 'a list) : 'a list2 option =
  match xs with
  | [] | _ :: [] -> None
  | x :: y :: [] -> Some (LastTwo (x, y))
  | x :: xs ->
      match to_list2 xs with
      | Some xs -> Some (Cons (x, xs))
      | None -> failwith "BUG in to_list2"

(* get_enum_info takes the type environment, enum name, optional type argument
 * (which only applies to option and list) and constructor name and returns:
 * - Left (named, index, typ) if the type defines a multi-constructor enum and
 *   named is the named type defining this enum, index is the constructor's
 *   index, and typ the constructor's type
 * - Right typ if nm defines a single-constructor enum, and typ is the type
 *   of the constructor
 *)
let get_enum_info (tys : type_env) (nm : string) (ty_arg : Ast.typ option)
  (constr : string)
  : (Target.namedTy * int * Target.typ, Target.typ) Either.t =
  let rec extract_enum_info (t : typ)
    : (Target.namedTy * int * Target.typ, Target.typ) Either.t =
    match t with
    | Enum (enum_name, constrs) ->
        begin match StringMap.find_opt constr constrs with
        | None -> failwith "Invalid constructor"
        | Some (idx, tys) -> 
            if StringMap.cardinal constrs = 1
            then Either.Right (target_type (Product tys))
            else let cases : (string * Target.typ) Array.t 
              = Array.make (StringMap.cardinal constrs) ("", Target.Primitive Unit)
            in StringMap.iter
              (fun nm (idx, tys) -> cases.(idx) <- (nm, target_type (Product tys)))
              constrs
            ; match to_list2 (Array.to_list cases) with
            | None -> failwith "enum does not have enough cases"
            | Some cs -> Either.Left (Cases (enum_name, cs), idx, snd cases.(idx))
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
  in match ty_arg with
  | None ->
      (* An enum defined in the environment *)
      begin match UniqueMap.find nm tys with
      | Some t -> extract_enum_info t
      | None -> failwith "undefined type"
      end
  | Some t ->
      (* Either a list::<t> or option::<t> *)
      let t = process_type t tys
      in match nm with
      | "list" -> extract_enum_info (List t)
      | "option" -> extract_enum_info (Option t)
      | _ -> failwith "undefined type constructor"

(* get_module_info takes the environment and an expression representing the
 * module name and returns a tuple of the information that forms the target
 * action for the module, the module's argument types, the module's input
 * struct definition, the module's return type, and the alias map for the
 * module's arguments
 *)
let get_module_info env (modul : Ast.expr)
  : Target.action * Target.typ StringMap.t * Target.structTy * Target.typ * string StringMap.t =
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
      let arg_types = StringMap.map target_type mod_info.argument_types
      in let struct_def = StringMap.map target_type mod_info.input_struct_def
      in let action_info : Target.action = 
        (String.concat "." mod_info.name,
         Struct struct_def,
         target_type mod_info.out_type,
         mod_info.body)
      in (action_info, arg_types, struct_def, target_type mod_info.out_type,
          mod_info.alias_map)

(* construct_enum generates the constructors needed for an enum constructor
 * identified by the given named type and constructor index *)
let construct_enum (enum : Target.namedTy) (idx : int) (e : Target.expr)
  : Target.expr =
  let rec construct_cases (enum_name : string) (cs : (string * Target.typ) list2)
    (idx : int) : Target.expr =
    match cs with
    | LastTwo (_, _) ->
        if idx = 0 then Function (Constructor (true, Cases (enum_name, cs)), e)
        else if idx = 1 then Function (Constructor (false, Cases (enum_name, cs)), e)
        else failwith "internal error: invalid index for enum"
    | Cons (_, r) ->
        if idx = 0 then Function (Constructor (true, Cases (enum_name, cs)), e)
        else Function (Constructor (false, Cases (enum_name, cs)),
                        construct_cases enum_name r (idx-1))
  in match enum with
  | List _ | Option _ ->
      if idx = 0 then Function (Constructor (true, enum), e)
      else if idx = 1 then Function (Constructor (false, enum), e)
      else failwith "internal error: invalid index for list or option"
  | Cases (enum_name, cs) -> construct_cases enum_name cs idx

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

let uniq () : int =
  let n = !tmp_counter
  in tmp_counter := n + 1
  ; n

(* Given a module variable information, determines whether we now know that a
 * certain variable must be available, and if so extracts it and evaluates k
 * in an updated environment *)
let update_module_var (info: bool * StringSet.t) input (locals: local_env)
  (k : local_env -> (Target.stmt, 'a) result) : (Target.stmt, 'a) result =
  let (required, vars) = info
  in if required && StringSet.cardinal vars = 1
  then
    let var = StringSet.min_elt vars
    in match StringMap.find_opt var locals with
    | Some (ModuleVar (_, ty)) ->
        let fresh_nm = fresh_var var
        in let new_env = StringMap.add var (LocalVar (fresh_nm, ty)) locals
        in Result.map (fun k: Target.stmt ->
           Match (Function (ReadField (input, var), Variable "#input"), fresh_nm,
                  Fail ("Variable " ^ var ^ " must be defined, but it isn't"),
                  k)
        ) (k new_env)
    | _ -> k locals
  else k locals

(* Update the locals environment to reflect that the variable var (which is a
 * member of the module variables with ID mod_id and options options) exists
 * and has been assigned the unique name nm and has type typ *)
let update_module_var_env (mod_id: int) (options: StringSet.t) (var: string)
  (nm: string) (typ: Target.typ) (env: local_env) : local_env =
  let rec helper (vars: string list) (env: local_env) : local_env =
    match vars with
    | [] -> env
    | v :: tl ->
        match StringMap.find_opt v env with
        | None | Some (LocalVar _) -> helper tl env
        | Some (ModuleVar (id, _)) -> if id <> mod_id then helper tl env
                                      else helper tl (StringMap.remove v env)
  in StringMap.add var (LocalVar (nm, typ))
        (helper (StringSet.to_list options) env)

(* process_expr takes a continuation which takes an expression and produces a
 * statement and then returns a statement. The reason for this is that some
 * expressions in the Module language requires statmenets in the calculus and
 * so we may have to build statments as we process the expression. This setup
 * will be placed before the statement generated by the continuation which can
 * use the result of the expression *)
let rec process_expr (e : Ast.expr) env tys locals (is_mod : mod_info option)
  (k : Target.expr * Target.typ -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  (* Our main helper function; it's continuation takes an "expr_result" which
   * contains at least one of an expression and a function to produce an
   * attribute; this is because of how we need to evaluate attributes. The
   * possibility of both an expression and attribute is needed to handle
   * attributes on attributes *)
  let rec process (e : Ast.expr)
    (k : expr_result -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match e with
    | Id nm       ->
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (name, typ)) -> k (JustExpr (Variable name, typ))
        | Some (ModuleVar _) -> Error ("variable " ^ nm ^ " may not be provided")
        | None -> Error ("undefined variable " ^ nm)
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
                    | _ -> Error "expected expression")
                | _ -> Error "expected expression")
        end
    | RecordExp (nm, fields) ->
        begin match nm with
        | Id nm ->
            begin match UniqueMap.find nm tys with
            | Some (Struct struct_def) ->
                let target_struct = StringMap.map target_type struct_def
                in let init_struct : Target.expr
                  = Function (EmptyStruct target_struct, Literal (Unit ()))
                in let filled_struct : Target.expr -> (Target.stmt, string) result
                  = List.fold_left 
                    (fun (k : Target.expr -> (Target.stmt, string) result)
                         (field, expr) record ->
                      if not (StringMap.mem field struct_def)
                      then Error ("unexpected field " ^ field)
                      else
                        process expr
                          (fun field_expr ->
                            match field_expr with
                            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                                if t <> StringMap.find field target_struct
                                then Error ("incorrect type for field " ^ field)
                                else
                                  k (Function
                                      (AddField (target_struct, field),
                                       Pair (record, e)))
                            | _ -> Error "expected expression"))
                    (fun e -> k (JustExpr (e, Struct target_struct)))
                    fields
                in filled_struct init_struct
            | _ -> Error "expected struct name"
            end
        | _ -> Error "expected struct name"
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
                                then Error ("incorrect type for field " ^ field)
                                else 
                                  k (JustExpr
                                    (Function
                                      (AddField (fields, field),
                                       Pair (e, f)),
                                     Struct fields))
                            | _ -> Error "expected expression")
                    | None -> Error ("type does not have field " ^ field)
                    end
                | _ -> Error "type has no fields"
                end
            | _ -> Error "expected expression")
    | EnumExp (enum, type_arg, constr, args) ->
        begin match enum with
        | Id enum ->
            begin match get_enum_info tys enum type_arg constr with
            | Either.Left (enum, idx, typ) ->
                process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> typ
                        then Error ("incorrect type for constructor " ^ constr)
                        else
                          k (JustExpr (construct_enum enum idx e, Named enum))
                    | _ -> Error "expected expression")
            | Either.Right typ -> process (ProductExp args)
                (fun a ->
                  match a with
                  | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                      if t <> typ
                      then Error ("incorrect type for constructor " ^ constr)
                      else k (JustExpr (e, t))
                  | _ -> Error "expected expression")
            end
        | _ -> Error "expected enum name"
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
                        then Error ("incorrect type for element " ^ nm)
                        else 
                          k (JustAttr (fun attr -> OnElement (elem, e, attr)))
                    | _ -> Error "expected expression")
            | Some (Uninterpreted (nm, in_tys, out_typ)) ->
                let in_ty = target_type (Product in_tys)
                and out_ty = target_type out_typ
                in process (ProductExp args)
                  (fun a ->
                    match a with
                    | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                        if t <> in_ty
                        then Error ("incorrect type for uninterpreted function " ^ nm)
                        else 
                          k (JustExpr (
                              Function (Uninterpreted (nm, in_ty, out_ty), e),
                              out_ty))
                    | _ -> Error "expected expression")
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
                        then Error ("incorrect type for function " ^ nm)
                        else
                          Result.bind (k (JustExpr (Variable tmp, ret_ty)))
                          (fun res ->
                           Ok (Target.Action (tmp, 
                                  (nm, arg_typ, ret_ty, body), e, res)))
                    | _ -> Error "expected expression")
            | Some _ -> Error "expected function"
            | None -> Error ("undefined name " ^ nm)
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
                          then Error "incorrect type on element"
                          else 
                            k (JustAttr (fun attr 
                              -> qual (OnElement (elem, e, attr))))
                      | _ -> Error "expected expression")
                    | JustExpr _ -> failwith "expected element")
            | Some _ -> Error "expected element"
            | None -> Error "undefined name"
            end
        | _ -> Error "invalid function expression"
        end
      | ModuleExp (func, args) ->
          let (mod_info, arg_types, record_def, ret_ty, aliases) 
            = get_module_info env func
          and tmp = temp_name ()
          in let init_input : Target.expr =
            Function (EmptyStruct record_def, Literal (Unit ()))
          in let assigned_args : (Ast.expr StringMap.t, string) result =
            List.fold_left
              (fun (args : (Ast.expr StringMap.t, string) result) (field, expr) ->
                let canonical =
                  match StringMap.find_opt field aliases with
                  | Some nm -> nm
                  | None -> field
                in if not (StringMap.mem canonical record_def)
                then Error ("unexpected argument " ^ canonical)
                else Result.bind args
                (fun args ->
                  if StringMap.mem canonical args
                  then Error ("multiple values for argument " ^ canonical)
                  else Ok (StringMap.add canonical expr args)
                )
              )
              (Ok StringMap.empty)
              args
          in Result.bind assigned_args
          (fun assigned_args ->
            let filled_args : Target.expr -> (Target.stmt, string) result =
              StringMap.fold
                (fun field ty (k : Target.expr -> (Target.stmt, string) result)
                     record ->
                  match StringMap.find_opt field assigned_args with
                  | Some e ->
                      process e
                      (fun field_expr ->
                        match field_expr with
                        | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                            if t <> ty
                            then
                              Error ("incorrect module argument type for " ^ field)
                            else
                              k (Function
                                  (AddField (record_def, field),
                                  Pair (record, option_some e ty)))
                        | _ -> failwith "expected expression")
                  | None ->
                      k (Function (AddField (record_def, field),
                                   Pair (record, option_none ty))))
                arg_types
                (fun e ->
                  Result.bind (k (JustExpr (Variable tmp, ret_ty)))
                  (fun rest -> Ok (Target.Action (tmp, mod_info, e, rest))))
            in filled_args init_input)
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
                    | None -> Error ("invalid field " ^ field)
                    end
                | _ -> Error "does not have fields"
                end
            | JustAttr qual ->
                begin match UniqueMap.find field env with
                | Some (Attribute (nm, typ)) ->
                    let attr = (nm, target_type typ)
                    and tmp = temp_name ()
                    in Result.map
                      (fun rest -> Target.Get (tmp, qual (AttrAccess attr), rest))
                      (k (ExprOrAttr (
                              (Variable tmp, snd attr),
                              fun a -> qual (OnAttribute (attr, a)))))
                | Some _ -> Error "expected attribute"
                | None -> Error ("undefined attribute " ^ field)
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
                      Error "field is either a struct field or an attribute"
                    else
                      let attr = (nm, target_type typ)
                      and tmp = temp_name ()
                      in Result.map
                        (fun rest -> Target.Get (tmp, qual (AttrAccess attr), rest))
                        (k (ExprOrAttr (
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
                        | None -> Error ("invalid field " ^ field)
                        end
                    | _ -> Error "does not have fields")
    | ProductField (lhs, idx) ->
        process lhs
          (fun e ->
            match e with
            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                let (res, res_ty) = construct_product_read e t idx
                in k (JustExpr (res, res_ty))
            | _ -> Error "expected expression")
    | UnaryExp (e, op) ->
        process e
          (fun e ->
            match e with
            | JustExpr (e, t) | ExprOrAttr ((e, t), _) ->
                begin match op with
                | Not ->
                    if t <> Primitive Bool
                    then Error "Incorrect type for negation"
                    else k (JustExpr (Function (BoolNeg, e), Primitive Bool))
                | _ -> Error "TODO: support unary -"
                end
            | _ -> Error "expected expression")
    | BinaryExp (_, _, _) -> Error "TODO: support binary ops"
    | CondExp (cond, thn, els) ->
        process cond
          (fun e ->
            match e with
            | JustExpr (c, t) | ExprOrAttr ((c, t), _) ->
                if t <> Primitive Bool
                then Error "non-boolean condition"
                else
                  let tmp = temp_name ()
                  in Result.map
                    (fun (thn, els) -> Target.Cond (c, thn, els))
                    (let thn_type = ref (Error "failure compiling then branch")
                    in let after = ref (Error "failure compiling then branch")
                    in let thn_stmt =
                      process thn (fun thn ->
                        match thn with
                        | JustExpr (thn, thn_t) | ExprOrAttr ((thn, thn_t), _) ->
                            thn_type := Ok thn_t
                            ; after := k (JustExpr (Variable tmp, thn_t))
                            ; Result.bind !after
                              (fun after -> Ok (Target.Assign (tmp, thn, after)))
                        | _ -> Error "expected expression")
                    in let els_stmt =
                      process els (fun els ->
                        match els with
                        | JustExpr (els, els_t) | ExprOrAttr ((els, els_t), _) ->
                            begin match !thn_type with
                            | Ok thn_t ->
                                if thn_t <> els_t
                                then Error "types of ternary branches do not match"
                                else Result.bind !after
                                  (fun after -> Ok (Target.Assign (tmp, els, after)))
                            | Error _ -> Error "failure compiling then branch"
                            end
                        | _ -> Error "expected expression")
                    in match thn_stmt, els_stmt with
                    | Ok thn, Ok els -> Ok (thn, els)
                    | Error err, _ -> Error err
                    | _, Error err -> Error err)
            | _ -> Error "expected expression")
    | CondProvidedExp (var, thn, els) ->
        begin match is_mod with
        | None -> Error "unexpected variable check"
        | Some (mod_env, input) ->
            match StringMap.find_opt var locals with
            | Some (LocalVar _) ->
                Error ("expected a module variable on if-provided, but "
                       ^ var ^ " is a local")
            | None -> Error ("variable " ^ var ^ " is undefined")
            | Some (ModuleVar (mod_id, typ)) ->
                let (required, options) = IntMap.find mod_id mod_env
                in let fresh_nm = fresh_var var
                in let false_mod_info = (required, StringSet.remove var options)
                in let false_mod_env = IntMap.add mod_id false_mod_info mod_env
                in let false_locals = StringMap.remove var locals
                in let true_locals
                  = update_module_var_env mod_id options var fresh_nm typ locals
                in let tmp = temp_name ()
                in update_module_var false_mod_info input false_locals
                  (fun false_locals ->
                    Result.map
                      (fun (thn, els) -> Target.Match 
                        (Function (ReadField (input, var), Variable "#input"),
                        fresh_nm, els, thn))
                    (let thn_type = ref (Error "failure compiling then branch")
                    in let after = ref (Error "failure compiling then branch")
                    in let thn_stmt =
                      process_expr thn env tys true_locals
                        (Some (mod_env, input))
                        (fun (thn, thn_t) ->
                          thn_type := Ok thn_t
                          ; after := k (JustExpr (Variable tmp, thn_t))
                          ; Result.bind !after
                            (fun after -> Ok (Target.Assign (tmp, thn, after))))
                    in let els_stmt =
                      process_expr els env tys false_locals 
                        (Some (false_mod_env, input))
                        (fun (els, els_t) ->
                          match !thn_type with
                          | Ok thn_t ->
                              if thn_t <> els_t
                              then Error "types of ternary branches do not match"
                              else Result.bind !after
                                (fun after -> Ok (Target.Assign (tmp, els, after)))
                          | Error _ -> Error "failure compiling then branch")
                    in match thn_stmt, els_stmt with
                    | Ok thn, Ok els -> Ok (thn, els)
                    | Error err, _ -> Error err
                    | _, Error err -> Error err))
        end
    | CondExistsExp (q, thn, els) ->
        process_expr_as_elem q env tys locals is_mod
          (fun elem ->
            let tmp = temp_name ()
            in Result.map
              (fun (thn, els) -> Target.Contains (elem, thn, els))
              (let thn_type = ref (Error "failure compiling then branch")
              in let after = ref (Error "failure compiling then branch")
              in let thn_stmt =
                process thn (fun thn ->
                  match thn with
                  | JustExpr (thn, thn_t) | ExprOrAttr ((thn, thn_t), _) ->
                      thn_type := Ok thn_t
                      ; after := k (JustExpr (Variable tmp, thn_t))
                      ; Result.bind !after 
                        (fun after -> Ok (Target.Assign (tmp, thn, after)))
                  | _ -> Error "expected expression")
              in let els_stmt =
                process els (fun els ->
                  match els with
                  | JustExpr (els, els_t) | ExprOrAttr ((els, els_t), _) ->
                      begin match !thn_type with
                      | Ok thn_t ->
                          if thn_t <> els_t
                          then Error "types of ternary branches do not match"
                          else Result.bind !after
                            (fun after -> Ok (Target.Assign (tmp, els, after)))
                      | Error _ -> Error "failure compiling then branch"
                      end
                  | _ -> Error "expected expression")
              in match thn_stmt, els_stmt with
              | Ok thn, Ok els -> Ok (thn, els)
              | Error err, _ -> Error err
              | _, Error err -> Error err))
  in process e
    (fun e ->
      match e with
      | JustExpr (e, t) | ExprOrAttr ((e, t), _) -> k (e, t)
      | JustAttr _ -> Error "Expected expression, not element")

and process_expr_as_elem (e : Ast.expr) env tys locals
  (is_mod : mod_info option) (k : Target.elem -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  let rec process_elem (q : Ast.expr) (e : Target.elem)
    (k : Target.elem -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match q with
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
                (fun (expr, typ) ->
                  if typ <> snd elem
                  then Error ("incorrect type on element " ^ nm)
                  else k (OnElement (elem, expr, e)))
        | _ -> Error ("Invalid element " ^ elem)
        end
    | FuncExp (Field (qual, elem), args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then Error ("incorrect type on element " ^ nm)
                else process_elem qual (OnElement (elem, expr, e)) k)
        | _ -> Error ("Invalid element " ^ elem)
        end
    | Field (qual, attr) ->
        begin match UniqueMap.find attr env with
        | Some (Attribute (nm, typ)) ->
            let attr = (nm, target_type typ)
            in process_elem qual (OnAttribute (attr, e)) k
        | _ -> Error ("Invalid attribute " ^ attr)
        end
    | _ -> Error "Invalid qualifier"
  in match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then Error ("incorrect type on element " ^ nm)
                else k (Element (elem, expr)))
      | _ -> Error ("Invalid element " ^ elem)
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then Error ("incorrect type on element " ^ nm)
              else process_elem qual (Element (elem, expr)) k)
      | _ -> Error ("Invalid element " ^ elem)
      end
  | _ -> Error "Invalid qualifier"

let rec process_qual (e : Ast.expr) env tys locals (is_mod : mod_info option)
  (q : Target.qual) (k : Target.qual -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then Error ("incorrect type in element " ^ nm)
                else k (Element (elem, expr, [q])))
      | _ -> Error ("Invalid element " ^ elem)
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then Error ("incorrect type in element " ^ nm)
              else process_qual qual env tys locals is_mod
                                (Element (elem, expr, [q])) k)
      | _ -> Error ("Invalid element " ^ elem)
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
      | _ -> Error ("Invalid attribute " ^ attr)
      end
  | _ -> Error "Invalid qualifier"

(* Process an expression for a clear statement (the final access is not an
   attribute) *)
let process_expr_as_qual (e : Ast.expr) env tys locals
  (is_mod : mod_info option) (k : Target.qual -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  match e with
  | FuncExp (Id elem, args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
              (fun (expr, typ) ->
                if typ <> snd elem
                then Error ("incorrect type on element " ^ nm)
                else k (Element (elem, expr, [])))
      | _ -> Error ("Invalid element " ^ elem)
      end
  | FuncExp (Field (qual, elem), args) ->
      begin match UniqueMap.find elem env with
      | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process_expr (ProductExp args) env tys locals is_mod
            (fun (expr, typ) ->
              if typ <> snd elem
              then Error ("incorrect type on element " ^ nm)
              else process_qual qual env tys locals is_mod
                                (Element (elem, expr, [])) k)
      | _ -> Error ("Invalid element " ^ elem)
      end
  | _ -> Error "Invalid qualifier"

let rec negate_qual (q : Target.qual) : Target.qual =
  match q with
  | Attribute (_, _, []) -> failwith "Cannot negate an attribute"
  | Attribute (a, e, qs) -> Attribute (a, e, List.map negate_qual qs)
  | Element (e, ex, []) -> NotElement (e, ex)
  | Element (e, ex, qs) -> Element (e, ex, List.map negate_qual qs)
  | NotElement (_, _) -> failwith "Cannot generate negated qual from front-end"

(* As we process l-values we either have have a value (such as a variable or a
 * field access) or we have an attribute *)
type lval_res =
  (* For values we return the type of the value, an expression which evaluates
   * its current value, and a continuation which builds the assignment to that
   * value for a given expression being assigned and statement to follow *)
  | LValue     of Target.typ * Target.expr
                * (Target.expr -> (Target.stmt, string) result
                               -> (Target.stmt, string) result)
  (* For attributes, we return both the attribute as a qualifier with other
   * elements/attributes following it and as the top-level attribute (which is
   * a continuation expecting the value being assigned) *)
  | LAttribute of ((Target.qual -> Target.qual) * (Target.attr -> Target.attr))
                * (Target.typ * Target.expr * (Target.expr -> Target.qual))
  | LElement   of (Target.qual -> Target.qual) * (Target.attr -> Target.attr)

let process_lval (e : Ast.expr) env tys locals (is_mod : mod_info option)
  (assigned : Target.expr) (typ : Target.typ) (k : (Target.stmt, string) result)
  : (Target.stmt, string) result =
  let rec process (e : Ast.expr) (k : lval_res -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
    match e with
    | Id nm ->
        (* Attributes are not supported on the top-level of the state, so an
         * identifier must be a local variable *)
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (var, typ)) ->
            k (LValue (typ, Variable var, 
                       fun e -> Result.map (fun s -> Target.Assign (var, e, s))))
        | Some _ -> Error ("variable " ^ nm ^ " may not be provided")
        | None -> Error ("undefined variable " ^ nm)
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
                    | None -> Error ("does not have field " ^ field)
                    end
                | _ -> Error "has no fields"
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
                | Some _, Some _ -> Error "ambiguous field or attribute"
                | None, None -> Error "undefined field or attribute"
                | Some (fields, field_ty), None ->
                    k (LValue (field_ty, 
                               Function (ReadField (fields, field), expr),
                               fun e -> Result.map (fun s -> Target.Add (as_assign e, s))))
                | None, Some attr ->
                    let tmp = temp_name ()
                    in Result.bind (k (LAttribute (
                        ((fun q
                          -> as_qual (Attribute (attr, Variable tmp, [q]))),
                         (fun a
                          -> as_attr (OnAttribute (attr, a)))),
                        (snd attr, Variable tmp,
                         fun e -> as_qual (Attribute (attr, e, []))))))
                    (fun rest ->
                      Ok (Target.Get (tmp, as_attr (AttrAccess attr), rest)))
                end
            | LElement (as_qual, as_attr) ->
                match UniqueMap.find field env with
                | Some (Attribute (nm, typ)) ->
                    let attr = (nm, target_type typ)
                    and tmp = temp_name ()
                    in Result.bind (k (LAttribute (
                        ((fun q
                          -> as_qual (Attribute (attr, Variable tmp, [q]))),
                         (fun a
                          -> as_attr (OnAttribute (attr, a)))),
                        (snd attr, Variable tmp,
                         fun e -> as_qual (Attribute (attr, e, []))))))
                    (fun rest ->
                      Ok (Target.Get (tmp, as_attr (AttrAccess attr), rest)))
                | _ -> Error "expected attribute")
    | ProductField (_lhs, _idx) -> Error "TODO: handle product field accesses"
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
            let elem = (nm, target_type typ)
            in process_expr (ProductExp args) env tys locals is_mod
              (fun (e, t) ->
                if t <> snd elem
                then Error ("incorrect type for element " ^ nm)
                else Result.bind (k 
                        (LElement ((fun q -> Element (elem, e, [q])),
                                  (fun a -> OnElement (elem, e, a)))))
                (fun after -> Ok (Target.Add (Element (elem, e, []), after))))
        | Some _ -> Error ("expected element, " ^ elem ^ " is not one")
        | _ -> Error ("undefined name " ^ elem)
        end
    | FuncExp (Field (lhs, elem), args) ->
        begin match UniqueMap.find elem env with
        | Some (Element (nm, typ)) ->
          let elem = (nm, target_type typ)
          in process lhs
            (fun res ->
              match res with
              | LValue (_, _, _) -> Error "cannot access element on value"
              | LAttribute ((as_qual, as_attr), _)
              | LElement   (as_qual, as_attr) ->
                  process_expr (ProductExp args) env tys locals is_mod
                  (fun (e, t) ->
                    if t <> snd elem
                    then Error ("incorrect type for element " ^ nm)
                    else Result.bind (k (LElement (
                            (fun q -> as_qual (Element (elem, e, [q]))),
                            (fun a -> as_attr (OnElement (elem, e, a))))))
                    (fun after -> 
                      Ok (Target.Add (as_qual (Element (elem, e, [])), after)))
                  ))
        | Some _ -> Error ("expected element " ^ elem ^ " is not one")
        | _ -> Error ("undefined name " ^ elem)
        end
    | _ -> Error "invalid l-value"
  in process e
    (fun res ->
      match res with
      | LValue (t, _, assign) ->
          if t <> typ
          then Error "incorrect type in assignment"
          else assign assigned k
      | LAttribute (_, (t, _, attr)) ->
          if t <> typ
          then Error "incorrect type in assignment"
          else Result.map (fun k -> Target.Add (attr assigned, k)) k
      | LElement _ -> Error "expected l-value, found element")

(* Given a list of names and a value and type constructs a target statement
 * which extracts fields and assigns them to the given names.
 * This is used since the calculus only allows single argument functions and
 * pattern matching. *)
let rec generateVarInits (names : string list) (ty : Target.typ)
    (exp : Target.expr) (locals : local_env)
    (k : local_env -> (Target.stmt, string) result)
    : (Target.stmt, string) result  =
  match names with
  | [] -> k locals
  | [n] ->
      let fresh_n = fresh_var n
      in Result.bind (k (StringMap.add n (LocalVar (fresh_n, ty)) locals))
         (fun rest -> Ok (Target.Assign (fresh_n, exp, rest)))
  | n :: ns ->
      match ty with
      | Product (x, y) ->
          let fresh_n = fresh_var n
          in Result.bind 
              (generateVarInits ns y (Function (Proj (false, x, y), exp))
                (StringMap.add n (LocalVar (fresh_n, x)) locals) k)
            (fun rest ->
              Ok (Target.Assign (fresh_n, Function (Proj (true, x, y), exp), rest)))
      | _ -> failwith "Type error"


type 'a processed = Default of 'a | Set of 'a

let of_processed (x : 'a processed) : 'a = match x with Default y | Set y -> y

let rec process_vars_codegen
  (vars : (string * string list * Ast.typ * Ast.expr option) list)
  : ((string * Ast.typ) list * (string * Ast.typ * Ast.expr) option, string) result =
  match vars with
  | [] -> Ok ([], None)
  | (v, _, t, None) :: tl ->
      Result.bind (process_vars_codegen tl)
        (fun (vs, default) -> Ok ((v, t) :: vs, default))
  | (v, _, t, Some d) :: tl ->
      Result.bind (process_vars_codegen tl)
        (fun (vs, default) ->
          match default with
          | None -> Ok ((v, t) :: vs, Some (v, t, d))
          | Some _ -> Error "multiple default values specified")

(* Given the input's record type, a list of variables, and a statements for
 * found and not found cases, construct match statements that execute the
 * found code if exactly one of the variables is defined, the not found code
 * if none of the variables are defined, and produces a failure if multiple
 * variables are defined *)
let generate_vars_check input (vars : (string * Ast.typ) list)
  (found : (Target.stmt, 'a) result) (not_found : (Target.stmt, 'a) result)
  : (Target.stmt, 'a) result =
  let vars = List.map fst vars
  in let rec helper vs need_var =
    match vs with
    | [] -> if need_var then not_found else found
    | v :: tl ->
        Result.bind (helper tl need_var)
          (fun if_not ->
            let if_some = if need_var then helper tl false
              else Ok (Fail ("Only one of [" ^ String.concat ", " vars
                             ^ "] should be provided"))
            in Result.bind if_some
            (fun if_some ->
              Ok (Target.Match (
                    Function (ReadField (input, v), Variable "#input"),
                    "_",
                    if_not,
                    if_some
            ))))
  in helper vars true

let init_stmt_k = Error "Reached end of statements, missing terminator"

(* process_stmt's is_mod argument specifies whether variable declarations
 * and checks are allowed in the code or not, so this function can be used to
 * generate code for both functions and modules. *)
(* The continuation (k) to these functions defines a statement that should come
 * at the end of the statements (such as the terminator for a loop or a return
 * for a unit-valued function). If it is not provided, reaching the end of
 * the list of statements will produce an error *)
let rec process_stmt (s : Ast.stmt list) env tys locals
  (is_mod : mod_info option) (k : (Target.stmt, string) result)
  : (Target.stmt, string) result  =
  match s with
  | [] -> k
  | VarDecls (required, vars) :: tl ->
      begin match is_mod with
      | None -> Error "unexpected variable check"
      | Some (mod_env, input) ->
          Result.bind (process_vars_codegen vars)
          (fun (vars, default) ->
          (* Any variable with a default is treated as required since it will
           * always have a value *)
          let var_info = (required || Option.is_some default,
                          StringSet.of_list (List.map fst vars))
          in let var_id = uniq ()
          in let new_mod_env = IntMap.add var_id var_info mod_env
          in let new_locals = 
            List.fold_left (fun env (var, typ) -> 
                  StringMap.add 
                    var
                    (ModuleVar (var_id, target_type (process_type typ tys)))
                    env)
              locals vars
          in let body = update_module_var var_info input new_locals
            (fun locals ->
              process_stmt tl env tys locals (Some (new_mod_env, input)) k)
          in match default with
          | None ->
              generate_vars_check input vars body
                (if required
                then Ok (Fail ("One of the arguments ["
                               ^ String.concat ", " (List.map fst vars)
                               ^ "] is required"))
                else body)
          | Some (var, typ, value) ->
              let typ = target_type (process_type typ tys)
              in process_expr value env tys locals is_mod
                (fun (value, ty) ->
                  if ty <> typ then Error ("default for " ^ var ^ " has wrong type")
                  else generate_vars_check input vars body
                  (* If there's a default and none of the variables are provided,
                   * set #input = #input[.var <- Some(value)] to initialize the
                   * variable with a default value *)
                  (Result.bind body
                    (fun body ->
                      Ok (Target.Assign ("#input",
                        Function (AddField (input, var),
                        Pair (Variable "#input", option_some value typ)),
                        body))))
                )
          )
      end
  | ForLoop (v, l, b) :: tl ->
      process_expr l env tys locals is_mod
        (fun (lst, typ) ->
          match typ with
          | Named (List t) ->
            let fresh_v = fresh_var v
            in let body_env = StringMap.add v (LocalVar (fresh_v, t)) locals
            in Result.bind 
              (process_stmt b env tys body_env is_mod (Ok (Return Env)))
              (fun body ->
                Result.bind (process_stmt tl env tys locals is_mod k)
                (fun after ->
                  Ok (Target.Loop (fresh_v, lst, body, after))))
          | _ -> Error "can only loop over lists")
  | IfProvided (var, thn, els) :: tl ->
      begin match is_mod with
      | None -> Error "unexpected variable check"
      | Some (mod_env, input) ->
        let after = process_stmt tl env tys locals is_mod k
        in match StringMap.find_opt var locals with
        | Some (LocalVar _) ->
            Error ("expected a module variable on if-provided, but "
                   ^ var ^ " is a local")
        | None -> Error ("variable " ^ var ^ " is undefined")
        | Some (ModuleVar (mod_id, typ)) ->
            let (required, options) = IntMap.find mod_id mod_env
            in let fresh_nm = fresh_var var
            in let false_mod_info = (required, StringSet.remove var options)
            in let false_mod_env = IntMap.add mod_id false_mod_info mod_env
            in let false_locals = StringMap.remove var locals
            in let true_locals
              = update_module_var_env mod_id options var fresh_nm typ locals
            in Result.bind
                (update_module_var false_mod_info input false_locals
                  (fun locals ->
                    process_stmt els env tys locals
                      (Some (false_mod_env, input)) after))
              (fun not_provided -> (* None = not provied = else case *)
                Result.bind (process_stmt thn env tys true_locals
                              (Some (mod_env, input)) after)
                (fun if_provided ->
                  Ok (Target.Match (
                        Function (ReadField (input, var), Variable "#input"),
                        fresh_nm,
                        not_provided,
                        if_provided
                  ))
                )
              )
      end
  | IfExists (q, thn, els) :: tl ->
      let after = process_stmt tl env tys locals is_mod k
      in process_expr_as_elem q env tys locals is_mod
        (fun elem ->
          Result.bind (process_stmt thn env tys locals is_mod after)
          (fun thn_stmt ->
            Result.bind (process_stmt els env tys locals is_mod after)
            (fun els_stmt ->
              Ok (Target.Contains (elem, thn_stmt, els_stmt)))))
  | IfThenElse (c, thn, els) :: tl ->
      let after = process_stmt tl env tys locals is_mod k
      in process_expr c env tys locals is_mod
          (fun (c, _) ->
            Result.bind (process_stmt thn env tys locals is_mod after)
            (fun thn_stmt ->
              Result.bind (process_stmt els env tys locals is_mod after)
              (fun els_stmt ->
                Ok (Target.Cond (c, thn_stmt, els_stmt)))))
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
                                               after))
                   | Set _ -> failwith "Duplicate case")
              cs
          ; process_expr e env tys locals is_mod
            (fun (e, _) ->
              (* FIXME: Check that the type is correct based on the patterns *)
              Result.bind (array_foldr1 (Array.map of_processed cases)
                (fun l r -> Result.bind l
                  (fun l -> Result.bind r
                    (fun r -> 
                      Ok (Target.Match (Variable "#match", "#match", l, r))))))
              (fun cases -> Ok (Target.Assign ("#match", e, cases))))
      end
  | Clear e :: tl ->
      process_expr_as_qual e env tys locals is_mod
        (fun q -> 
          Result.bind (process_stmt tl env tys locals is_mod k)
            (fun after -> Ok (Target.Add (negate_qual q, after))))
  | Assert e :: tl ->
      process_expr e env tys locals is_mod
        (fun (e, _) ->
          Result.bind (process_stmt tl env tys locals is_mod k)
            (fun rest -> Ok (Target.Cond (e, rest, Fail "assertion failed"))))
  | AssertExists q :: tl ->
      process_expr_as_elem q env tys locals is_mod
        (fun elem ->
          Result.bind (process_stmt tl env tys locals is_mod k)
            (fun rest ->
              Ok (Target.Contains (elem, rest, Fail "assertion failed"))))
  | Return _ :: _ :: _ -> Error "Code after return"
  | Return e :: [] ->
      process_expr e env tys locals is_mod (fun (e, _) -> Ok (Target.Return e))
  | LetStmt (var, exp) :: tl ->
      process_expr exp env tys locals is_mod
        (fun (e, t) ->
          let fresh_var = fresh_var var
          in let locals = StringMap.add var (LocalVar (fresh_var, t)) locals
          in Result.bind (process_stmt tl env tys locals is_mod k)
            (fun rest -> Ok (Target.Assign (fresh_var, e, rest))))
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
        in add_type nm (Enum (nm, variants)) env; create_types tl env
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
        let (aliases, ast_types, var_types, struct_def)
          = process_module_for_args body types
        and ret_ty = process_type_option ret types
        and mod_body = ref None
        in let mod_info =
          { name = nm;
            alias_map = aliases;
            args = ast_types;
            argument_types = var_types;
            input_struct_def = struct_def;
            out_type = ret_ty;
            body = mod_body }
        in add_modules nm (Module mod_info) env
        ; (Either.Right (body, struct_def), ret_ty, mod_body)
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
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error ("Reached end of statements, missing terminator")
        in
        body_ref :=
          Some (unwrap
            (generateVarInits args arg_ty (Variable "#input")
                empty_local_env
                (fun locals ->
                    process_stmt body env types locals None default_ret)))
        ; process_functions tl env types
    (* Module body *)
    | (Either.Right (body, input), ret_type, body_ref) :: tl ->
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error ("Reached end of statements, missing terminator")
        in
        body_ref := 
          Some(unwrap(process_stmt body env types empty_local_env
                (Some (empty_mod_env, StringMap.map target_type input))
                default_ret))
        ; process_functions tl env types

  in let (tys, dfs, fns) = partition files
  in let type_env = UniqueMap.empty ()
  in let global_env : global_env = UniqueMap.empty ()
  in create_types tys type_env
  ; create_definitions dfs type_env global_env
  ; process_functions (create_functions fns type_env global_env) global_env type_env
  ; (type_env, global_env)

let codegen_program (body : Ast.stmt list) tys env : Target.stmt =
  unwrap
    (process_stmt body env tys empty_local_env None
        (Ok (Return (Literal (Unit ())))))

(* Looks up a module's definition given its name and a global environment
 * Returns None if it could not be found for any reason *)
let find_module_def (name : string list) (env : global_env)
  : module_info option =
  let rec helper name entry =
    match name with
    | [] ->
        begin match entry with
        | Module mod_info -> Some mod_info
        | _ -> None
        end
    | nm :: name ->
        match entry with
        | Environment env ->
            begin match UniqueMap.find nm env with
            | None -> None
            | Some entry -> helper name entry
            end
        | _ -> None
  in helper name (Environment env)
