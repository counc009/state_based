let ( let^ ) r f = Result.bind r f

type 'a list2 = 'a Target.list2

module IntMap    = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module TargetAst = Target
module Target = Target.Ast_Target

module UniqueMap = struct
  type 'a t = (string, 'a) Hashtbl.t

  let empty () = Hashtbl.create 10

  let find (key : string) (map : 'a t) : 'a option =
    Hashtbl.find_opt map key

  let add (key : string) (value : 'a) (map : 'a t) : (unit, string) result =
    match find key map with
    | Some _ -> Error (Printf.sprintf "key %s already defined" key)
    | _ -> Ok (Hashtbl.add map key value)
end

type 'a placeholder = 'a option ref

type typ = Bool | Int | Float | String | Path | Unit
         | Option      of typ
         | List        of typ
         | Product     of typ list
         (* Store the name of the struct along with the info on its fields *)
         | Struct      of string * typ StringMap.t
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
    ret_type: Ast.typ;
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

type except_env = typ UniqueMap.t

type context =
  { types: type_env
  ; globals: global_env
  ; excepts: except_env }

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

(* Some helper functions *)
let foreach_res (xs : 'a list) (f : 'a -> (unit, 'e) result)
  : (unit, 'e) result =
  let rec foreach (xs : 'a list) : (unit, 'e) result =
    match xs with
    | [] -> Ok ()
    | x :: xs -> Result.bind (f x) (fun () -> foreach xs)
  in foreach xs

let foreachs_res (xs : 'a list list) (f : 'a -> (unit, 'e) result)
  : (unit, 'e) result =
  let rec foreach (xs : 'a list) : (unit, 'e) result =
    match xs with
    | [] -> Ok ()
    | x :: xs -> Result.bind (f x) (fun () -> foreach xs)
  in let rec foreach_list (xs : 'a list list) : (unit, 'e) result =
    match xs with
    | [] -> Ok ()
    | xs :: tl -> Result.bind (foreach xs) (fun () -> foreach_list tl)
  in foreach_list xs

let map_res (f : 'a -> ('b, 'e) result) (xs : 'a list) : ('b list, 'e) result =
  let rec step (xs : 'a list) : ('b list, 'e) result =
    match xs with
    | [] -> Ok []
    | x :: xs ->
        Result.bind (f x) (fun y ->
          Result.bind (step xs) (fun ys ->
            Ok (y :: ys)))
  in step xs

let mapi_res (f : int -> 'a -> ('b, 'e) result) (xs : 'a list)
  : ('b list, 'e) result =
  let rec step (xs : 'a list) (i : int) : ('b list, 'e) result =
    match xs with
    | [] -> Ok []
    | x :: xs ->
        Result.bind (f i x) (fun y ->
          Result.bind (step xs (i + 1)) (fun ys ->
            Ok (y :: ys)))
  in step xs 0

let flatmap_res (f : 'a -> ('b, 'e) result) (xs : 'a list list)
  : ('b list, 'e) result =
  let rec map (xs : 'a list) (acc : 'b list) : ('b list, 'e) result =
    match xs with
    | [] -> Ok acc
    | x :: xs ->
        let^ y = f x
        in let^ ys = map xs acc
        in Ok (y :: ys)
  in let rec flatmap (xs : 'a list list) : ('b list, 'e) result =
    match xs with
    | [] -> Ok []
    | xs :: tl -> Result.bind (flatmap tl) (fun acc -> map xs acc)
  in flatmap xs

let smap_map_res (f : 'a -> ('b, 'e) result) (m : 'a StringMap.t)
  : ('b StringMap.t, 'e) result =
  StringMap.fold (fun s x res -> Result.bind res (fun res ->
    Result.bind (f x) (fun y ->
      Ok (StringMap.add s y res))))
    m
    (Ok StringMap.empty)

(* create_type (and its related functions) convert an Ast.typ into an internal
 * typ, and if an unknown type name is encountered in the process will insert
 * that type as a placeholder into the type_env. This helps address issues
 * with cyclical types and avoids needing to properly order files as they are
 * processed. *)
let create_type (t : Ast.typ) (env : type_env) : (typ, string) result =
  let rec create (t : Ast.typ) : (typ, string) result =
    match t with
    | Bool -> Ok Bool
    | Int -> Ok Int
    | Float -> Ok Float
    | String -> Ok String
    | Path -> Ok Path
    | Unit -> Ok Unit
    | Product ts ->
        Result.bind (map_res create ts) (fun ts -> Ok (Product ts))
    | List t ->
        Result.bind (create t) (fun t -> Ok (List t))
    | Option t ->
        Result.bind (create t) (fun t -> Ok (Option t))
    | Named nm ->
        match UniqueMap.find nm env with
        | Some t -> Ok t
        | None ->
            let res = Placeholder (ref None)
            in Result.bind (UniqueMap.add nm res env) (fun () -> Ok res)
  in create t

let create_types_option (ts : Ast.typ list option) (env : type_env)
    : (typ list, string) result =
  match ts with
  | None -> Ok []
  | Some ts -> map_res (fun t -> create_type t env) ts

(* process_type, like create_type, converts an Ast.typ into an internal typ,
 * but process_type is used once we have collected all types and so any
 * unrecognized type name is an error *)
let process_type (t : Ast.typ) (env : type_env) : (typ, string) result =
  let rec process (t : Ast.typ) =
    match t with
    | Bool -> Ok Bool
    | Int -> Ok Int
    | Float -> Ok Float
    | String -> Ok String
    | Path -> Ok Path
    | Unit -> Ok Unit
    | Product ts ->
        Result.bind (map_res process ts) (fun ts -> Ok (Product ts))
    | List t ->
        Result.bind (process t) (fun t -> Ok (List t))
    | Option t ->
        Result.bind (process t) (fun t -> Ok (Option t))
    | Named nm ->
        match UniqueMap.find nm env with
        | Some t -> Ok t
        | None -> Error (Printf.sprintf "undefined type %s" nm)
  in process t

let process_type_option (t : Ast.typ option) (env : type_env)
  : (typ, string) result =
  match t with
  | None -> Ok Unit
  | Some t -> process_type t env

(* lower_type and its relatives convert an internal type into a target type *)
let rec lower_type (t : typ) : (Target.typ, string) result =
  match t with
  | Bool -> Ok (Primitive Bool)
  | Int -> Ok (Primitive Int)
  | Float -> Ok (Primitive Float)
  | String -> Ok (Primitive String)
  | Path -> Ok (Primitive Path)
  | Unit -> Ok (Primitive Unit)
  | Option t ->
      Result.bind (lower_type t) (fun t -> Ok (Target.Named (Option t)))
  | List t ->
      Result.bind (lower_type t) (fun t -> Ok (Target.Named (List t)))
  | Product ts -> lower_types ts
  | Struct (_, fs) ->
      Result.bind (smap_map_res lower_type fs)
        (fun fs : (Target.typ, string) result -> Ok (Struct fs))
  | Enum (nm, cs) -> lower_sum nm cs
  | Placeholder t ->
      match !t with
      | None -> Error "Missing type definition"
      | Some t -> lower_type t
and lower_types (ts : typ list) : (Target.typ, string) result =
  match ts with
  | [] -> Ok (Primitive Unit)
  | [t] -> lower_type t
  | t :: ts ->
      let^ t = lower_type t
      in let^ ts = lower_types ts
      in Ok (Target.Product (t, ts))
and lower_sum (enum_name : string) (cs : (int * typ list) StringMap.t)
  : (Target.typ, string) result =
  let types : (string * typ list) array
    = Array.make (StringMap.cardinal cs) ("", [])
  in let () =
    List.iter
      (fun (nm, (i, ts)) -> types.(i) <- (nm, ts))
      (StringMap.to_list cs)
  in if Array.length types = 0
  then Ok (Primitive Unit)
  else if Array.length types = 1
  then lower_types (snd types.(0))
  else
    let rec lower_cases (cs : (string * typ list) list)
      : ((string * Target.typ) list2, string) result =
      match cs with
      | [] | [_] -> Error "Internal Error: Expected at least two cases"
      | (nm1, ts1) :: (nm2, ts2) :: [] ->
          let^ ts1 = lower_types ts1
          in let^ ts2 = lower_types ts2
          in Ok (LastTwo ((nm1, ts1), (nm2, ts2)) : _ list2)
      | (nm, ts) :: cs ->
          let^ ts = lower_types ts
          in let^ cs = lower_cases cs
          in Ok (Cons ((nm, ts), cs) : _ list2)
    in Result.bind (lower_cases (Array.to_list types)) (fun cs ->
        Ok (Target.Named (Cases (enum_name, cs))))

let extract_module_args (body : Ast.stmt list) (types : type_env)
  : (string StringMap.t * Ast.typ StringMap.t * typ StringMap.t
      * typ StringMap.t, string) result =
  let add_vars vars info =
    let add_alias (alias : string) (nm : string) aliases =
      match StringMap.find_opt alias aliases with
      | None -> Ok (StringMap.add alias nm aliases)
      | Some n ->
          if n = nm then Ok aliases
          else Error (Printf.sprintf
              "Variable %s already used as alias for different canonical name"
              alias)
    in let add_aliases nms nm aliases =
      List.fold_left (fun aliases alias -> Result.bind aliases (fun aliases -> 
        add_alias alias nm aliases))
        (Ok aliases) nms
    in let add_var nm alias typ info =
      let (aliases, ast_types, var_types, struct_def) = info
      in let ast_types = StringMap.add nm typ ast_types
      in let^ typ = process_type typ types
      in let^ var_types =
        match StringMap.find_opt nm aliases with
        | Some _ ->
            Error (Printf.sprintf "Variable %s already used as alias" nm)
        | None ->
            match StringMap.find_opt nm var_types with
            | None -> Ok (StringMap.add nm typ var_types)
            | Some t ->
                if type_equality t typ then Ok var_types
                else Error (Printf.sprintf
                        "Variable %s already used with different type" nm)
      in let^ aliases = add_aliases alias nm aliases
      in let struct_def = StringMap.add nm (Option typ) struct_def
      in Ok (aliases, ast_types, var_types, struct_def)
    in List.fold_left (fun info (nm, alias, typ, _) ->
        Result.bind info (fun info -> add_var nm alias typ info))
        (Ok info) vars
  in let rec extract_stmt (s : Ast.stmt) info =
    match s with
    | VarDecls (_, vars) -> add_vars vars info
    | ForLoop (_, _, body) -> extract body info
    | IfProvided (_, thn, els) | IfExists (_, thn, els)
    | IfThenElse (_, thn, els) ->
        let^ new_info = extract thn info in extract els new_info
    | Match (_, cases) ->
        List.fold_left (fun info (_, case) ->
          Result.bind info (fun info -> extract case info))
          (Ok info) cases
    | TryCatch (body, catch, finally) ->
        let^ info_body = extract body info
        in let^ info_catch =
          match catch with
          | None -> Ok info_body
          | Some (_, _, catch) -> extract catch info_body
        in extract finally info_catch
    | _ -> Ok info
  and extract (body : Ast.stmt list) info =
    match body with
    | [] -> Ok info
    | s :: tl ->
        let^ new_info = extract_stmt s info in extract tl new_info
  in extract body
      (StringMap.empty, StringMap.empty, StringMap.empty, StringMap.empty)

let rec generate_var_inits (names : string list) (ty : Target.typ)
  (exp : Target.expr) (locals : local_env)
  : (Target.stmt * local_env, string) result =
  match names with
  | [] -> Ok (Pass, locals)
  | [n] ->
      let fresh_n = fresh_var n
      in let new_env = StringMap.add n (LocalVar (fresh_n, ty)) locals
      in let setup = Target.Assign (fresh_n, exp)
      in Ok (setup, new_env)
  | n :: ns ->
      match ty with
      | Product (x, y) ->
          let fresh_n = fresh_var n
          in let new_env = StringMap.add n (LocalVar (fresh_n, x)) locals
          in let setup_n =
            Target.Assign (fresh_n, Function (Proj (true, x, y), exp))
          in let snd : Target.expr = Target.Function (Proj (false, x, y), exp)
          in Result.bind (generate_var_inits ns y snd new_env)
            (fun (setup, locals) -> Ok (Target.Seq (setup_n, setup), locals))
      | _ -> Error "Internal Type Error in generate_var_inits"

let codegen_stmts (s : Ast.stmt list) (types : type_env) (globals : global_env)
  (excepts : except_env) (locals : local_env) (ret : Target.typ)
  (yield : Target.typ placeholder option) (is_mod : mod_info option)
  (* A terminator to insert at the end of the stmts, unless another terminator
   * is encountered. *)
  (term : (Target.stmt, string) result) : (Target.stmt, string) result =

  let rec codegen_stmt (s : Ast.stmt) (locals : local_env)
    (yield : Target.typ placeholder option) (is_mod : mod_info option)
    : (Target.stmt * local_env * mod_info option, string) result =
    match s with
    | VarDecls (required, vars) ->
        begin match is_mod with
        | None -> Error "Module-style variable declaration in function"
        | Some (mod_env, input) ->
            Error "TODO"
        end
    | _ -> Error "TODO"

  and codegen_stmts (s : Ast.stmt list) (locals : local_env)
    (yield : Target.typ placeholder option) (is_mod : mod_info option)
    : (Target.stmt, string) result =
    match s with
    | [] -> term
    | s :: tl ->
        let^ (res_s, new_locals, new_mod) = codegen_stmt s locals yield is_mod
        in let^ res_tl = codegen_stmts tl new_locals yield new_mod
        in Ok (Target.Seq (res_s, res_tl))

  in codegen_stmts s locals yield is_mod

(* Main driver function, given the result of parsing a bunch of files (hence a
 * list of lists of top-levels), we produce return the context which contains
 * types, globals, and exceptions defined by those files. *)
let codegen (parsed : Ast.topLevel list list) : (context, string) result =
  let types = UniqueMap.empty ()
  in let globals = UniqueMap.empty ()
  in let excepts = UniqueMap.empty ()

  in let insert_type (nm : string) (t : typ) : (unit, string) result =
    match UniqueMap.find nm types with
    | Some (Placeholder p) -> Ok (p := Some t)
    | _ -> UniqueMap.add nm t types

  in let insert_module (nm : string list) (t : env_entry)
    : (unit, string) result =
    let rec insert (nm : string list) (env : global_env)
      : (unit, string) result =
      match nm with
      | [] -> Error "Internal Error: empty module name"
      | [n] -> UniqueMap.add n t env
      | n :: tl ->
          match UniqueMap.find n env with
          | Some (Environment env) -> insert tl env
          | Some _ -> Error "Prefix of module name already exists"
          | None ->
              let new_env = UniqueMap.empty ()
              in let^ () = UniqueMap.add n (Environment new_env) env
              in insert tl new_env
    in insert nm globals

  (* Helper functions, which add types (enums, records, and type aliases),
   * definitions (attributes, elements, exceptions, and uninterpreted functions),
   * and functions (both functions and modules) to the appropriate environments *)
  in let add_type (t : Ast.topLevel) : (unit, string) result =
    match t with
    | Enum (nm, variants) ->
        let^ variants =
          Result.bind
            (mapi_res
              (fun i (nm, ts) ->
                Result.bind (create_types_option ts types) (fun ts ->
                  Ok (nm, (i, ts))))
              variants)
            (fun vs -> Ok (StringMap.of_list vs))
        in insert_type nm (Enum (nm, variants))
    | Struct (nm, fields) ->
        let^ fields =
          Result.bind
            (map_res (fun (nm, t) ->
              Result.bind (create_type t types) (fun t -> Ok (nm, t)))
              fields)
            (fun fs -> Ok (StringMap.of_list fs))
        in insert_type nm (Struct (nm, fields))
    | Type (nm, typ) ->
        Result.bind (create_type typ types) (fun ty ->
          insert_type nm ty)
    | _ -> Ok ()
  in let add_def (t : Ast.topLevel) : (unit, string) result =
    match t with
    | Uninterp (nm, in_tys, out_ty) ->
        let^ in_tys = map_res (fun t -> process_type t types) in_tys
        in let^ out_typ = process_type out_ty types
        in UniqueMap.add nm (Uninterpreted (nm, in_tys, out_typ)) globals
    | Attribute (nm, ty) ->
        Result.bind (process_type ty types) (fun typ ->
          UniqueMap.add nm (Attribute (nm, typ)) globals)
    | Element (nm, ty) ->
        Result.bind (process_type ty types) (fun typ ->
          UniqueMap.add nm (Element (nm, typ)) globals)
    | Exception (nm, ty) ->
        Result.bind (process_type ty types) (fun typ ->
          UniqueMap.add nm typ excepts)
    | _ -> Ok ()
  in let add_func (t : Ast.topLevel) : (_ option, string) result =
    match t with
    | Function (nm, args, ret, body) ->
        let^ arg_tys = map_res (fun (_, t) -> process_type t types) args
        in let^ ret_ty = process_type_option ret types
        in let func_body = ref None
        in let^ arg_ty = lower_types arg_tys
        in let^ () =
          UniqueMap.add nm (Function (nm, arg_ty, ret_ty, func_body)) globals
        in Ok (Some (Either.Left (body, List.map fst args, arg_ty),
                      ret_ty, func_body))
    | Module (nm, alt_names, ret, body) ->
        let^ (aliases, ast_types, var_types, struct_def) =
          extract_module_args body types
        in let^ ret_ty = process_type_option ret types
        in let mod_body = ref None
        in let mod_info : module_info =
          { name = nm
          ; alias_map = aliases
          ; args = ast_types
          ; argument_types = var_types
          ; input_struct_def = struct_def
          ; out_type = ret_ty
          ; ret_type = (match ret with None -> Product [] | Some t -> t)
          ; body = mod_body }
        in let^ () = insert_module nm (Module mod_info)
        in let^ () =
          foreach_res alt_names (fun nm -> insert_module nm (Module mod_info))
        in Ok (Some (Either.Right (body, struct_def), ret_ty, mod_body))
    | _ -> Ok None

  in let codegen_func f : (unit, string) result =
    match f with
    | None -> Ok ()
    (* Function body *)
    | Some (Either.Left (body, args, arg_ty), ret_type, body_ref) ->
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error "Reached end of function body, no return"
        (* Because the calculus only allows a single arguments for everything,
         * we generate code that reads each argument out of the initial tuple
         * passed in as the #input argument *)
        in let^ (setup, locals) =
          generate_var_inits args arg_ty (Variable "#input") empty_local_env
        in let^ ret_type = lower_type ret_type
        in let^ func_body =
          codegen_stmts body types globals excepts locals ret_type None
            None default_ret
        in Ok (body_ref := Some (func_body))
    (* Module body *)
    | Some (Either.Right (body, input), ret_type, body_ref) ->
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error "Reached end of module body, no return"
        in let^ ret_type = lower_type ret_type
        in let^ input_type = smap_map_res lower_type input
        in let^ func_body =
          codegen_stmts body types globals excepts empty_local_env ret_type
            None (Some (empty_mod_env, input_type)) default_ret
        in Ok (body_ref := Some (func_body))

  in let^ () = foreachs_res parsed add_type
  in let^ () = foreachs_res parsed add_def
  in let^ funcs = flatmap_res add_func parsed
  in let^ () = foreach_res funcs codegen_func
  in Ok { types = types; globals = globals; excepts = excepts }
