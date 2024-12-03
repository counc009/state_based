(* TODO: Fix error handling *)

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

type env_entry = Variable of typ
               | Attribute of string * typ
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

(* process_stmt is used to handle statements in functions/Ansible (and loop
 * bodies in modules) while process_module is used to handle statements in
 * module definitions which are allowed to contain variable declarations *)
(* TODO *)
let process_stmt (_s : Ast.stmt list) _env : Target.stmt = Return Env
let process_module (_s : Ast.stmt list) _env : Target.stmt = Return Env

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
            (List.map
              (fun (i, (nm, ts)) -> (nm, (i, create_types_option ts env)))
              (List.mapi (fun i x -> (i, x)) variants))
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
  in let rec process_functions ts env =
    match ts with
    | [] -> ()
    (* Function body *)
    | (Either.Left (body, args, arg_ty), body_ref) :: tl ->
        (* Because the calculus just has a single argument for everything we
           generate code that reads each argument out of the initial argument
           #input *)
        body_ref :=
          Some (generateVarInits args arg_ty (Variable "#input")
                    (process_stmt body env))
        ; process_functions tl env
    (* Module body *)
    | (Either.Right body, body_ref) :: tl ->
        body_ref := Some(process_module body env)
        ; process_functions tl env

  in let (tys, dfs, fns) = partition files
  in let type_env = UniqueMap.empty ()
  in let global_env : global_env = UniqueMap.empty ()
  in create_types tys type_env
  ; create_definitions dfs type_env global_env
  ; process_functions (create_functions fns type_env global_env) global_env
  ; (type_env, global_env)
