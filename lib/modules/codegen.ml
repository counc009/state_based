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

  let fold f (m : 'a t) x = Hashtbl.fold f m x
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

type env_entry =
  (* Attributes and Elements have whether they are local and then their name
   * and type *)
  | Attribute of bool * string * typ
  | Element of bool * string * typ
  | Uninterpreted of string * typ list * typ
  (* Function has its argument type and then return type *)
  | Function of string * Target.typ * typ * Target.stmt placeholder
  | Module of module_info
  (* Environment is used to create a multi-level environment to handle fully
   * qualified names *)
  | Environment of global_env
and global_env = env_entry UniqueMap.t

type except_env = typ UniqueMap.t

type context =
  { types: type_env
  ; globals: global_env
  ; excepts: Target.typ StringMap.t }

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
let rec to_list2 (xs : 'a list) : 'a list2 option =
  match xs with
  | [] | _ :: [] -> None
  | x :: y :: [] -> Some (LastTwo (x, y))
  | x :: xs ->
      match to_list2 xs with
      | Some xs -> Some (Cons (x, xs))
      | None -> failwith "INTERNAL ERROR in to_list2"

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

let array_foldr1 (arr : 'a array) (f : 'a -> 'b) (g : 'b -> 'b -> 'b) : 'b =
  let rec process (i : int) : 'b =
    if i + 1 = Array.length arr
    then f arr.(i)
    else g (f arr.(i)) (process (i+1))
  in process 0

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

let lower_ast_typ (t : Ast.typ) (types : type_env)
  : (Target.typ, string) result = Result.bind (process_type t types) lower_type

(* Utilities for dealing with types and the type environment *)
(* Extract the constructors from an enum type *)
let rec extract_enum (t : typ)
  : ((int * typ list) StringMap.t, string) result =
  match t with
  | Enum (_, res) -> Ok res
  | Option t ->
      Ok (StringMap.of_list [("nothing", (0, [])); ("some", (1, [t]))])
  | List t ->
      Ok (StringMap.of_list [("nil", (0, [])); ("cons", (1, [t; List t]))])
  | Placeholder { contents = Some t } -> extract_enum t
  | _ -> Error "Not an enum type"

(* Return the constructors for a given enum type and type argument *)
let lookup_enum (types : type_env) (nm : string) (ty_arg : Ast.typ option)
  : ((int * typ list) StringMap.t, string) result =
  match ty_arg with
  | None ->
      (* An enum defined in the environment *)
      begin match UniqueMap.find nm types with
      | None -> Error ("Undefined type " ^ nm)
      | Some t -> extract_enum t
      end
  | Some t ->
      (* Either a list::<t> or option::<t> *)
      let^ t = process_type t types
      in match nm with
      | "list" ->
          Ok (StringMap.of_list [("nil", (0, [])); ("cons", (1, [t; List t]))])
      | "option" ->
          Ok (StringMap.of_list [("nothing", (0, [])); ("some", (1, [t]))])
      | _ -> Error ("Undefined type constructor " ^ nm)

(* get_enum_info returns:
 * - Left (named, index, typ) if the type defines a multi-constructor enum and
 *   named is the named type defining this enum, index is the constructor's
 *   index, and typ is the constructor's type.
 * - Right (typ) if nm defines a single-constructor enum and typ is the type
 *   of that constructor.
 *)
let get_enum_info (types : type_env) (nm : string) (ty_arg : Ast.typ option)
  (constr : string)
  : ((Target.namedTy * int * Target.typ, Target.typ) Either.t, string) result =
  let rec extract_enum_info (t : typ) =
    match t with
    | Enum (enum_name, constrs) ->
        begin match StringMap.find_opt constr constrs with
        | None -> Error ("No constructor " ^ constr ^ " for enum " ^ nm)
        | Some (idx, tys) ->
            if StringMap.cardinal constrs = 1
            then Result.bind (lower_type (Product tys))
                  (fun t -> Ok (Either.Right t))
            else let cases : (string * Target.typ) Array.t =
              Array.make (StringMap.cardinal constrs)
                ("", Target.Primitive Unit)
            in let^ () =
              StringMap.fold (fun nm (idx, tys) u ->
                Result.bind u (fun () ->
                  let^ t = lower_type (Product tys)
                  in Ok (cases.(idx) <- (nm, t))))
                constrs (Ok ())
            in match to_list2 (Array.to_list cases) with
            | None -> failwith "INTERNAL ERROR: enum lacks enough cases"
            | Some cs ->
                Ok (Either.Left (
                  (Cases (enum_name, cs) : Target.namedTy),
                  idx, snd cases.(idx)))
        end
    | Option t ->
        let^ typ = lower_type t
        in begin match constr with
        | "nothing" -> Ok (Either.Left ((Option typ : Target.namedTy), 0, Target.Primitive Unit))
        | "some"    -> Ok (Either.Left (Option typ, 1, typ))
        | _ -> Error ("No constructor " ^ constr ^ " for option")
        end
    | List t ->
        let^ typ = lower_type t
        in begin match constr with
        | "nil"  -> Ok (Either.Left ((List typ : Target.namedTy), 0, Target.Primitive Unit))
        | "cons" -> Ok (Either.Left (List typ, 1, Product (typ, Named (List typ))))
        | _ -> Error ("No constructor " ^ constr ^ " for list")
        end
    | Placeholder { contents = Some t } -> extract_enum_info t
    | _ -> Error "Type is not an enum"

  in match ty_arg with
  | None ->
      (* An enum defined in the environment *)
      begin match UniqueMap.find nm types with
      | Some t -> extract_enum_info t
      | None -> Error ("Undefined type " ^ nm)
      end
  | Some t ->
      (* Either a list<t> or option<t> *)
      let^ t = process_type t types
      in match nm with
      | "list" -> extract_enum_info (List t)
      | "option" -> extract_enum_info (Option t)
      | _ -> Error ("Undefined type constructor " ^ nm)

(* Return information for a given struct type *)
let lookup_struct (types : type_env) (nm : string)
  : (typ StringMap.t, string) result =
  let rec extract_struct (t : typ) =
    match t with
    | Struct (_, struct_def) -> Ok struct_def
    | Placeholder { contents = Some t } -> extract_struct t
    | _ -> Error (Printf.sprintf "%s is not a struct type " nm)
  in match UniqueMap.find nm types with
  | None -> Error ("Undefined type " ^ nm)
  | Some t -> extract_struct t

let lookup_module_info (nm : Ast.expr) (globals : global_env)
  : (Target.action * Target.typ StringMap.t * Target.structTy * Target.typ
      * string StringMap.t, string) result =
  let rec find_module (nm : Ast.expr)
    : ((global_env, module_info) Either.t, string) result =
    match nm with
    | Id nm ->
        begin match UniqueMap.find nm globals with
        | Some (Module mod_info) -> Ok (Either.Right mod_info)
        | Some (Environment env) -> Ok (Either.Left env)
        | Some _ -> Error "Not a module"
        | None   -> Error "Module name not defined"
        end
    | Field (nm, field) ->
        let^ env = find_module nm
        in begin match env with
        | Either.Right _ -> Error "Module name not defined"
        | Either.Left env ->
            match UniqueMap.find field env with
            | Some (Module mod_info) -> Ok (Either.Right mod_info)
            | Some (Environment env) -> Ok (Either.Left env)
            | Some _ -> Error "Not a module"
            | None   -> Error "Module name not defined"
        end
    | _ -> Error "Not a module name"
  in let^ res = find_module nm
  in match res with
  | Either.Left _ -> Error "Not a module"
  | Either.Right mod_info ->
      let^ arg_types = smap_map_res lower_type mod_info.argument_types
      in let^ struct_def = smap_map_res lower_type mod_info.input_struct_def
      in let^ out_ty = lower_type mod_info.out_type
      in let action_info : Target.action =
        (String.concat "." mod_info.name,
         Struct struct_def,
         out_ty,
         mod_info.body)
      in Ok (action_info, arg_types, struct_def, out_ty, mod_info.alias_map)

(* Given an enum name and possible type argument, check that it matches a
 * target type *)
let pattern_type_matches (types : type_env) (type_name, type_arg)
  (t : Target.typ) : bool =
  match type_arg with
  | None ->
      begin match t with
      | Named (Cases (enum_name, _)) when enum_name = type_name -> true
      | _ -> false
      end
  | Some ty_arg ->
      match t with
      | Named (List t) when type_name = "list" ->
          begin match lower_ast_typ ty_arg types with
          | Error _ -> false
          | Ok ty -> ty = t
          end
      | Named (Option t) when type_name = "option" ->
          begin match lower_ast_typ ty_arg types with
          | Error _ -> false
          | Ok ty -> ty = t
          end
      | _ -> false

(* Code analysis *)
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

(* Utilities for generating expressions *)
let floatlit (f : float) : Target.expr = Literal (Float f)
let intlit (i : int) : Target.expr = Literal (Int i)
let stringlit (s : string) : Target.expr = Literal (String s)

let option_some (e : Target.expr) (t : Target.typ) : Target.expr =
  Function (Constructor (false, Option t), e)

let option_none (t : Target.typ) : Target.expr =
  Function (Constructor (true, Option t), Literal (Unit ()))

let construct_enum (enum : Target.namedTy) (idx : int) (e : Target.expr)
  : Target.expr =
  match enum with
  | List _ | Option _ ->
      if idx = 0 then Function (Constructor (true, enum), e)
      else if idx = 1 then Function (Constructor (false, enum), e)
      else
        failwith "INTERNAL ERROR: Invalid index for list or option constructor"
  | Cases (enum_name, cs) ->
      let rec construct_cases (cs : (string * Target.typ) list2) (idx : int)
        : Target.expr =
        match cs with
        | LastTwo (_, _) ->
            if idx = 0
            then Function (Constructor (true, Cases (enum_name, cs)), e)
            else if idx = 1
            then Function (Constructor (false, Cases (enum_name, cs)), e)
            else failwith "INTERNAL ERROR: Invalid index for enum constructor"
        | Cons (_, r) ->
            if idx = 0
            then Function (Constructor (true, Cases (enum_name, cs)), e)
            else Function (Constructor (false, Cases (enum_name, cs)),
                  construct_cases r (idx - 1))
      in construct_cases cs idx

(* construct_product_read takes a product expression, its type, and an index
 * and generates an expression to fetch the desired index *)
let rec construct_product_read (e : Target.expr) (t : Target.typ) (i : int)
  : (Target.expr * Target.typ, string) result =
  match t with
  | Product (x, y) ->
      if i = 0
      then Ok (Function (Proj (true, x, y), e), x)
      else construct_product_read (Function (Proj (false, x, y), e)) y (i - 1)
  | _ ->
      if i = 0
      then Ok (e, t)
      else Error "No such field of product"

(* construct_product_access takes a product type and an index and identifes
 * the type of that index and produces functions that will read and write
 * to that field *)
let rec construct_product_access (t : Target.typ) (i : int)
  : (Target.typ
    * (Target.expr -> Target.expr) (* read *)
    * (Target.expr -> Target.expr -> Target.expr) (* write prod val *),
    string) result =
  match t with
  | Product (x, y) ->
      if i = 0
      then Ok (x, (fun p -> Function (Proj (true, x, y), p)),
            (fun p e -> Pair (e, Function (Proj (false, x, y), p))))
      else
        let^ (t, read, write) = construct_product_access y (i - 1)
        in Ok (t,
            (fun p -> read (Function (Proj (false, x, y), p) : Target.expr)),
            (fun p e ->
              (Pair (Function (Proj (true, x, y), p),
                write (Function (Proj (false, x, y), p) : Target.expr) e)
                  : Target.expr)))
  | _ ->
      if i = 0
      then Ok (t, (fun e -> e), (fun _p e -> e))
      else Error "No such field of product"

(* Utilities for dealing with elements, attributes, and qualifiers *)
let rec negate_qual (q : Target.qual) : (Target.qual, string) result =
  match q with
  | Attribute (_, _) -> Error "Cannot negate an attribute"
  | Element (e, ex, None) -> Ok (NotElement (e, ex))
  | Element (e, ex, Some q) ->
      Result.bind (negate_qual q)
        (fun nq -> Ok (Element (e, ex, Some nq) : Target.qual))
  | NotElement (e, ex) -> Ok (Element (e, ex, None))

let rec qual_to_attr (q : Target.qual) : (Target.attr, string) result =
  match q with
  | Attribute (attr, _) -> Ok (AttrAccess attr)
  | Element (_, _, None) -> Error "Not an attribute"
  | Element (elem, e, Some q) ->
      let^ attr = qual_to_attr q
      in Ok (OnElement (elem, e, attr) : Target.attr)
  | NotElement (_, _) -> Error "Not an attribute"

let local_attr (a : Target.attr) : Target.attr =
  OnElement (("#local", Primitive Unit), Literal (Unit ()), a)

let local_qual (q : Target.qual) : Target.qual =
  Element (("#local", Primitive Unit), Literal (Unit ()), Some q)

(* Utilities for generating certain statements *)

(* For exceptions, we have a special function we use to construct exception
 * values *)
let raise (exc : string) (e : Target.expr) (excepts : Target.typ StringMap.t)
  : Target.stmt =
  Raise (Function (GenExcept (excepts, exc), e))

let fatal (msg : string) (excepts : Target.typ StringMap.t) : Target.stmt =
  raise "!FATAL" (stringlit msg) excepts

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

let generate_vars_check (input : Target.typ StringMap.t)
  (vars : (string * Target.typ) list) (not_found : Target.stmt)
  (excepts : Target.typ StringMap.t): Target.stmt =

  let vars = List.map fst vars

  in let rec check_vars (vs : string list)
    (found : Target.stmt) (not_found : Target.stmt)  : Target.stmt =
    match vs with
    | [] -> not_found
    | v :: vs ->
        Target.Match (
          Function (ReadField (input, v), Variable "#input"),
          "_",
          check_vars vs found not_found,
          check_vars vs 
            (fatal ("Only one of [" ^ String.concat ", " vars 
                   ^ "] should be provided") excepts)
            found)

  in check_vars vars Pass not_found

(* Utilities for dealing with module arguments *)
let update_module_var (decl_info : bool * StringSet.t) input
  (locals : local_env) (excepts : Target.typ StringMap.t)
  : local_env * Target.stmt =
  let (required, vars) = decl_info
  in if required && StringSet.cardinal vars = 1
  then
    let var = StringSet.min_elt vars
    in match StringMap.find_opt var locals with
    | Some (ModuleVar (_, ty)) ->
        let fresh_nm = fresh_var var
        in let new_env = StringMap.add var (LocalVar (fresh_nm, ty)) locals
        in let load_var : Target.stmt =
          Match (Function (ReadField (input, var), Variable "#input"),
            fresh_nm,
            fatal ("Variable " ^ var ^ " must be defined, but it isn't") excepts,
            Pass)
        in (new_env, load_var)
    | _ -> (locals, Pass)
  else (locals, Pass)

(* Update the local environment to reflect that the variable var was chosen
 * for a declaration that has other options *)
let select_module_var (var : string) (mod_id : int) (options : StringSet.t)
  (nm : string) (typ : Target.typ) (env : local_env) : local_env =

  let rec remove_vars (vs : string list) (env : local_env) : local_env =
    match vs with
    | [] -> env
    | v :: tl ->
        remove_vars tl
          (match StringMap.find_opt v env with
          | None | Some (LocalVar _) -> env
          | Some (ModuleVar (id, _)) ->
              if id = mod_id
              then StringMap.remove v env
              else env)

  in StringMap.add var (LocalVar (nm, typ))
      (remove_vars (StringSet.to_list options) env)

(* A p_elem (or partial element) represents part of an element as we process
 * it from beginning (outermost) to end (innermost) *)
type p_elem = {
  as_elem : Target.elem option -> Target.elem;
  as_qual : Target.qual option -> Target.qual;
  as_attr : Target.attr -> Target.attr
}

let p_elem_top (is_local : bool) (el : Target.element) (ex : Target.expr)
  : p_elem =
  { as_elem = (fun o ->
      match o with
      | None   ->
          if is_local
          then OnElement (("#local", Primitive Unit), Literal (Unit ()),
                  Element (el, ex))
          else Element (el, ex)
      | Some e ->
          if is_local
          then OnElement (("#local", Primitive Unit), Literal (Unit ()),
                OnElement (el, ex, e))
          else OnElement (el, ex, e))
  ; as_qual = (fun o ->
      if is_local
      then Element (("#local", Primitive Unit), Literal (Unit ()),
            Some (Element (el, ex, o)))
      else Element (el, ex, o))
  ; as_attr = (fun o ->
      if is_local
      then OnElement (("#local", Primitive Unit), Literal (Unit ()),
            OnElement (el, ex, o))
      else OnElement (el, ex, o)) }

let p_elem_add (q : p_elem) (el : Target.element) (ex : Target.expr) : p_elem =
  { as_elem = (fun o ->
      match o with None   -> q.as_elem (Some (Element (el, ex)))
                 | Some e -> q.as_elem (Some (OnElement (el, ex, e))))
  ; as_qual = (fun o -> q.as_qual (Some (Element (el, ex, o))))
  ; as_attr = (fun o -> q.as_attr (OnElement (el, ex, o))) }

(* The result of our internal expression processing *)
type expr_result = Expr  of Target.expr * Target.typ
                 | Attr  of Target.attr * Target.typ
                 | Elem  of p_elem

let as_expr (r : expr_result)
  (k : Target.expr * Target.typ -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  match r with
  | Expr (e, t) -> k (e, t)
  | Attr (a, t) ->
      let tmp = temp_name ()
      in Result.bind (k (Variable tmp, t)) (fun s ->
        Ok (Target.Seq (Get (tmp, a), s)))
  | Elem _ -> Error "Element cannot be converted to expression"

(* process_expr converts an expr in the module lanugage into an expr_result,
 * but returns a statement using the continuation k since some expressions
 * in the Module language involved statements in the calculus (like reading
 * attributes) *)
let process_expr (e : Ast.expr) (types : type_env) (globals : global_env)
  (excepts : Target.typ StringMap.t) (locals : local_env)
  (is_mod : mod_info option)
  (codegen_stmts : Ast.stmt list -> local_env -> Target.typ placeholder option
      -> mod_info option -> (Target.stmt, string) result)
  (k : expr_result -> (Target.stmt, string) result)
  : (Target.stmt, string) result =

  let rec process (e : Ast.expr) (locals : local_env)
    (is_mod : mod_info option)
    (k : expr_result -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match e with
    | Id nm ->
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (name, typ)) -> k (Expr (Variable name, typ))
        | Some (ModuleVar _) ->
            Error ("Variable " ^ nm ^ " may not be provided")
        | None ->
            (* If it's not a local, it could be a top-level attribute *)
            match UniqueMap.find nm globals with
            | Some (Attribute (is_local, nm, typ)) ->
                let^ attr =
                  Result.bind (lower_type typ) (fun t -> Ok (nm, t))
                in if is_local
                then k (Attr (local_attr (AttrAccess attr), snd attr))
                else k (Attr (AttrAccess attr, snd attr))
            | _ -> Error ("Variable " ^ nm ^ " is undefined")
        end
    | BoolLit   v -> k (Expr (Literal (Bool v), Primitive Bool))
    | IntLit    v -> k (Expr (Literal (Int v), Primitive Int))
    | FloatLit  v -> k (Expr (Literal (Float v), Primitive Float))
    | StringLit v -> k (Expr (Literal (String v), Primitive String))
    | PathLit   v -> k (Expr (Literal (Path v), Primitive Path))
    | UnitExp     -> k (Expr (Literal (Unit ()), Primitive Unit))
    | GenUniversal t ->
        let^ ty = lower_ast_typ t types
        in k (Expr (Function (GenUniversal ty, Literal (Unit ())), ty))
    | GenExistential t ->
        let^ ty = lower_ast_typ t types
        in k (Expr (Function (GenExistential ty, Literal (Unit ())), ty))
    | ProductExp es ->
        begin match es with
        | [] -> k (Expr (Literal (Unit ()), Primitive Unit))
        | [e] -> process e locals is_mod k
        | e :: es ->
            process e locals is_mod (fun e ->
              as_expr e (fun (e, t) ->
                process (ProductExp es) locals is_mod (fun es ->
                  as_expr es (fun (es, ts) ->
                    k (Expr (Pair (e, es), Product (t, ts)))))))
        end
    | RecordExp (nm, fields) ->
        begin match nm with
        | Id nm ->
            let^ struct_def = lookup_struct types nm
            in let^ target_struct = smap_map_res lower_type struct_def
            in let init_struct : Target.expr =
              Function (EmptyStruct target_struct, Literal (Unit ()))
            in List.fold_left
              (fun (k : Target.expr -> (Target.stmt, string) result)
                   (field, expr) record ->
                match StringMap.find_opt field target_struct with
                | None -> Error ("No field " ^ field ^ " of type " ^ nm)
                | Some ft ->
                    process expr locals is_mod (fun e ->
                      as_expr e (fun (e, t) ->
                        if t <> ft
                        then Error ("Incorrect type for field " ^ field)
                        else
                          k (Function (AddField (target_struct, field),
                              Pair (record, e))))))
              (fun e -> k (Expr (e, Struct target_struct)))
              fields
              init_struct
        | _ -> Error "Expected a struct name"
        end
    | FieldSetExp (record, field, expr) ->
        process record locals is_mod (fun r ->
          as_expr r (fun (r, rt) ->
            match rt with
            | Struct fields ->
                begin match StringMap.find_opt field fields with
                | Some ft ->
                    process expr locals is_mod (fun e ->
                      as_expr e (fun (e, t) ->
                        if t <> ft
                        then Error ("Incorrect type for field " ^ field)
                        else
                          k (Expr (Function (AddField (fields, field),
                                    Pair (r, e)),
                              Struct fields))))
                | None -> Error ("Record does not have field " ^ field)
                end
            | _ -> Error "Expression is not a record"))
    | EnumExp (enum, type_arg, constr, args) ->
        begin match enum with
        | Id enum ->
            let^ enum_info = get_enum_info types enum type_arg constr
            in begin match enum_info with
            | Either.Left (enum, idx, typ) ->
                process (ProductExp args) locals is_mod (fun es ->
                  as_expr es (fun (e, t) ->
                    if t <> typ
                    then Error ("Incorrect type for constructor " ^ constr)
                    else
                      k (Expr (construct_enum enum idx e, Named enum))))
            | Either.Right typ ->
                process (ProductExp args) locals is_mod (fun es ->
                  as_expr es (fun (e, t) ->
                    if t <> typ
                    then Error ("Incorrect type for constructor " ^ constr)
                    else k (Expr (e, t))))
            end
        | _ -> Error "Expected an enum name"
        end
    | FuncExp (func, args) ->
        begin match func with
        | Field (q, nm) ->
            begin match UniqueMap.find nm globals with
            | Some (Element (_, nm, tys)) ->
                let^ elem = Result.bind (lower_type tys) (fun t -> Ok (nm, t))
                in process q locals is_mod (fun q ->
                  match q with
                  | Elem q ->
                      process (ProductExp args) locals is_mod (fun a ->
                        as_expr a (fun (e, t) ->
                          if t <> snd elem
                          then Error ("Incorrect type for element " ^ nm)
                          else k (Elem (p_elem_add q elem e))))
                  | _ -> Error "Can only access element on an element")
            | Some _ -> Error (nm ^ " is not an element")
            | None -> Error (nm ^ " is not defined")
            end
        | Id nm ->
            begin match UniqueMap.find nm globals with
            | Some (Element (is_local, nm, tys)) ->
                let^ elem = Result.bind (lower_type tys) (fun t -> Ok (nm, t))
                in process (ProductExp args) locals is_mod (fun a ->
                    as_expr a (fun (e, t) ->
                      if t <> snd elem
                      then Error ("Incorrect type for element " ^ nm)
                      else k (Elem (p_elem_top is_local elem e))))
            | Some (Uninterpreted (nm, in_tys, out_typ)) ->
                let^ in_ty = lower_type (Product in_tys)
                in let^ out_ty = lower_type out_typ
                in process (ProductExp args) locals is_mod (fun a ->
                    as_expr a (fun (e, t) ->
                      if t <> in_ty
                      then Error ("Incorrect type for uninterpreted function " ^ nm)
                      else k (Expr (Function (
                                Uninterpreted (nm, in_ty, out_ty), e), 
                                out_ty))))
            | Some (Function (nm, arg_typ, ret_typ, body)) ->
                (* Function calls are translated into statements because
                 * functions actually become actions in the calculus *)
                let^ ret_ty = lower_type ret_typ
                in let tmp = temp_name ()
                in process (ProductExp args) locals is_mod (fun a ->
                  as_expr a (fun (e, t) ->
                    if t <> arg_typ
                    then Error ("Incorrect argument type for function " ^ nm)
                    else
                      let^ res_k = k (Expr (Variable tmp, ret_ty))
                      in Ok (Target.Seq (
                              Action (tmp, (nm, arg_typ, ret_ty, body), e),
                              res_k))))
            | Some _ -> Error (nm ^ " is not a function")
            | None ->
                let^ (arg_typ, ret_typ, func) = Builtins.lookup_builtin nm
                in process (ProductExp args) locals is_mod (fun a ->
                    as_expr a (fun (e, t) ->
                      if t <> arg_typ
                      then Error ("Incorrect type for function " ^ nm)
                      else k (Expr (Function (func, e), ret_typ))))
            end
        | _ -> Error "Invalid function expression"
        end
    | ModuleExp (func, args) ->
        let^ (mod_info, arg_types, record_def, ret_ty, aliases) =
          lookup_module_info func globals
        in let tmp = temp_name ()
        in let init_input : Target.expr =
          Function (EmptyStruct record_def, Literal (Unit ()))
        in let^ assigned_args : Ast.expr StringMap.t =
          List.fold_left (fun (args : (Ast.expr StringMap.t, string) result)
            (field, expr) -> Result.bind args (fun args ->
              let canonical =
                match StringMap.find_opt field aliases with
                | Some nm -> nm
                | None -> field
              in if not (StringMap.mem canonical record_def)
              then Error ("Unexpected argument " ^ canonical)
              else if StringMap.mem canonical args
              then Error ("Multiple values for argument " ^ canonical)
              else Ok (StringMap.add canonical expr args)))
            (Ok StringMap.empty)
            args
        in StringMap.fold (fun field ty 
            (k : Target.expr -> (Target.stmt, string) result) record ->
              match StringMap.find_opt field assigned_args with
              | Some e ->
                  process e locals is_mod (fun e ->
                    as_expr e (fun (e, t) ->
                      if t <> ty
                      then
                        Error ("Incorrect type for module argument " ^ field)
                      else
                        k (Function (AddField (record_def, field),
                            Pair (record, option_some e ty)))))
              | None ->
                  k (Function (AddField (record_def, field),
                      Pair (record, option_none ty))))
            arg_types
            (fun e ->
              let^ k = k (Expr (Variable tmp, ret_ty))
              in Ok (Target.Seq (Action (tmp, mod_info, e), k)))
            init_input
    | Field (lhs, field) ->
        process lhs locals is_mod (fun e ->
          match e with
          | Elem elem ->
              (* We must be accessing an attribute *)
              begin match UniqueMap.find field globals with
              | Some (Attribute (_, nm, typ)) ->
                  let^ attr = 
                    Result.bind (lower_type typ) (fun t -> Ok (nm, t))
                  in k (Attr (elem.as_attr (AttrAccess attr), snd attr))
              | Some _ -> Error (field ^ " is not an attribute")
              | None -> Error ("Undefined attribute " ^ field)
              end
          (* Otherwise, we must be accessing a field from a record *)
          | _ ->
              as_expr e (fun (e, t) ->
                match t with
                | Struct fields ->
                    begin match StringMap.find_opt field fields with
                    | Some ty ->
                        k (Expr (Function (ReadField (fields, field), e), ty))
                    | None -> Error ("Record does not have field " ^ field)
                    end
                | _ -> Error "Expression is not a record"))
    | ProductField (lhs, idx) ->
        process lhs locals is_mod (fun e ->
          as_expr e (fun (e, t) ->
            let^ (res, res_ty) = construct_product_read e t idx
            in k (Expr (res, res_ty))))
    | UnaryExp (e, op) ->
        process e locals is_mod (fun e ->
          as_expr e (fun (e, t) ->
            match op with
            | Not ->
                if t <> Primitive Bool
                then Error "Incorrect type for boolean not"
                else k (Expr (Function (BoolNeg, e), Primitive Bool))
            | Neg ->
                match t with
                | Primitive Int ->
                    let neg : Target.expr =
                      Function (SubInt, Pair (intlit 0, e))
                    in k (Expr (neg, Primitive Int))
                | Primitive Float ->
                    let neg : Target.expr =
                      Function (SubFloat, Pair (floatlit 0.0, e))
                    in k (Expr (neg, Primitive Float))
                | _ -> Error "Invalid type for negation"))
    | BinaryExp (lhs, rhs, op) ->
        process lhs locals is_mod (fun lhs -> as_expr lhs (fun (lhs, lhs_t) ->
          process rhs locals is_mod (fun rhs -> as_expr rhs (fun (rhs, rhs_t) ->
            let^ (ret_type, f) =
              let simple f (x : Target.expr) y : Target.expr =
                Function (f, Pair (x, y))
              in match op with
              | Concat ->
                  if lhs_t = Target.Primitive String
                  && rhs_t = Target.Primitive String
                  then Ok (Target.Primitive String, simple TargetAst.Concat)
                  else Error "Incorrect type for concat"
              | Eq ->
                  if lhs_t = rhs_t
                  then Ok (Target.Primitive Bool, simple (TargetAst.Equal lhs_t))
                  else Error "Incompatible types for equality"
              | Ne ->
                  if lhs_t = rhs_t
                  then Ok (Target.Primitive Bool,
                            fun x y -> 
                              Target.Function (TargetAst.BoolNeg,
                                Function (TargetAst.Equal lhs_t,
                                  Pair (x, y))))
                  else Error "Incompatible types for inequality"
              | Append ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Named (List elem) ->
                        Ok (lhs_t, simple (TargetAst.Append elem))
                    | _ -> Error "Expected list types for append"
                  else Error "Incompatible types for append"
              | Add ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (lhs_t, simple TargetAst.AddInt)
                    | Target.Primitive Float ->
                        Ok (lhs_t, simple TargetAst.AddFloat)
                    | _ -> Error "Cannot add non-numeric types"
                  else Error "Types of add must be the same"
              | Sub ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (lhs_t, simple TargetAst.SubInt)
                    | Target.Primitive Float ->
                        Ok (lhs_t, simple TargetAst.SubFloat)
                    | _ -> Error "Cannot subtract non-numeric types"
                  else Error "Types of subtract must be the same"
              | Mul ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (lhs_t, simple TargetAst.MulInt)
                    | Target.Primitive Float ->
                        Ok (lhs_t, simple TargetAst.MulFloat)
                    | _ -> Error "Cannot multiply non-numeric types"
                  else Error "Types of multiply must be the same"
              | Div ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (lhs_t, simple TargetAst.DivInt)
                    | Target.Primitive Float ->
                        Ok (lhs_t, simple TargetAst.DivFloat)
                    | _ -> Error "Cannot divide non-numeric types"
                  else Error "Types of divide must be the same"
              | Mod ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (lhs_t, simple TargetAst.Modulo)
                    | Target.Primitive Float ->
                        Error "Cannot take the modulo of a float"
                    | _ -> Error "Cannot modulo non-numeric types"
                  else Error "Types of modulo must be ints"
              | Or ->
                  if lhs_t = Target.Primitive Bool
                  && rhs_t = Target.Primitive Bool
                  then Ok (Target.Primitive Bool, simple TargetAst.BoolOr)
                  else Error "Types for or must be booleans"
              | And ->
                  if lhs_t = Target.Primitive Bool
                  && rhs_t = Target.Primitive Bool
                  then Ok (Target.Primitive Bool, simple TargetAst.BoolAnd)
                  else Error "Types for and must be booleans"
              | Lt ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (Target.Primitive Bool, simple TargetAst.LtInt)
                    | Target.Primitive Float ->
                        Ok (Target.Primitive Bool, simple TargetAst.LtFloat)
                    | _ -> Error "Cannot compare non-numeric types"
                  else Error "Types for comparisons must be the same"
              | Le ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (Target.Primitive Bool, simple TargetAst.LeInt)
                    | Target.Primitive Float ->
                        Ok (Target.Primitive Bool, simple TargetAst.LeFloat)
                    | _ -> Error "Cannot compare non-numeric types"
                  else Error "Types for comparisons must be the same"
              | Gt ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (Target.Primitive Bool,
                          fun x y -> (* x > y *)
                            Target.Function (TargetAst.LtInt,
                              Pair (y, x)))
                    | Target.Primitive Float ->
                        Ok (Target.Primitive Bool, 
                          fun x y ->
                            Target.Function (TargetAst.LtFloat,
                              Pair (y, x)))
                    | _ -> Error "Cannot compare non-numeric types"
                  else Error "Types for comparisons must be the same"
              | Ge ->
                  if lhs_t = rhs_t
                  then
                    match lhs_t with
                    | Target.Primitive Int ->
                        Ok (Target.Primitive Bool,
                          fun x y -> (* x >= y *)
                            Target.Function (TargetAst.LeInt,
                              Pair (y, x)))
                    | Target.Primitive Float ->
                        Ok (Target.Primitive Bool,
                          fun x y ->
                            Target.Function (TargetAst.LeFloat,
                              Pair (y, x)))
                    | _ -> Error "Cannot compare non-numeric types"
                  else Error "Types for comparisons must be the same"
              | LShift ->
                  if lhs_t = Target.Primitive Int
                  && rhs_t = Target.Primitive Int
                  then Ok (Target.Primitive Int, simple TargetAst.LShift)
                  else Error "Cannot shift non-integers"
              | RShift ->
                  if lhs_t = Target.Primitive Int
                  && rhs_t = Target.Primitive Int
                  then Ok (Target.Primitive Int, simple TargetAst.RShift)
                  else Error "Cannot shift non-integers"
            in k (Expr (f lhs rhs, ret_type))))))
    | CondExp (cond, thn, els) ->
        process cond locals is_mod (fun c -> as_expr c (fun (c, t) ->
          if t <> Primitive Bool
          then Error "Condition must be a boolean value"
          else
            let tmp = temp_name ()
            in let thn_type = ref (Target.Primitive Unit)
            in let^ thn_stmt =
              process thn locals is_mod (fun thn ->
                as_expr thn (fun (thn, thn_t) ->
                  thn_type := thn_t ; Ok (Target.Assign (tmp, thn))))
            in let^ els_stmt =
              process els locals is_mod (fun els ->
                as_expr els (fun (els, els_t) ->
                  if els_t <> !thn_type
                  then Error "Types of ternary branches must match"
                  else Ok (Target.Assign (tmp, els))))
            in let^ res_k = k (Expr (Variable tmp, !thn_type))
            in Ok (Target.Seq (Cond (c, thn_stmt, els_stmt), res_k))))
    | CondProvidedExp (var, thn, els) ->
        begin match is_mod with
        | None -> Error "Module-style variable check in function"
        | Some (mod_env, input) ->
            match StringMap.find_opt var locals with
            | Some (LocalVar _) ->
                Error ("Variable " ^ var ^ " is a local, not a module variable")
            | None -> Error ("Variable " ^ var ^ " is undefined")
            | Some (ModuleVar (mod_id, typ)) ->
                let (required, options) = IntMap.find mod_id mod_env
                in let fresh_nm = fresh_var var
                in let false_decl_info =
                  (required, StringSet.remove var options)
                in let false_mod_env =
                  IntMap.add mod_id false_decl_info mod_env
                in let (false_locals, false_start) =
                  update_module_var false_decl_info input
                    (StringMap.remove var locals) excepts
                in let true_locals =
                  select_module_var var mod_id options fresh_nm typ locals

                in let tmp = temp_name ()
                in let thn_type = ref (Target.Primitive Unit)
                in let^ thn_stmt =
                  process thn true_locals is_mod (fun thn ->
                    as_expr thn (fun (thn, thn_t) ->
                      thn_type := thn_t ; Ok (Target.Assign (tmp, thn))))
                in let^ els_stmt =
                  process els false_locals (Some (false_mod_env, input))
                  (fun els ->
                    as_expr els (fun (els, els_t) ->
                      if els_t <> !thn_type
                      then Error "Types of ternary branches must match"
                      else Ok (Target.Assign (tmp, els))))
                in let^ res_k = k (Expr (Variable tmp, !thn_type))
                in Ok (Target.Seq (
                        Match (
                          Function (ReadField (input, var), Variable "#input"),
                          fresh_nm,
                          Seq (false_start, els_stmt),
                          thn_stmt),
                        res_k))
        end
    | CondExistsExp (q, thn, els) ->
        process q locals is_mod (fun q ->
          match q with
          | Expr (_, _) | Attr (_, _) -> Error "Not an element"
          | Elem elem ->
              let elem = elem.as_elem None
              in let tmp = temp_name ()
              in let thn_type = ref (Target.Primitive Unit)
              in let^ thn_stmt =
                process thn locals is_mod (fun thn ->
                  as_expr thn (fun (thn, thn_t) ->
                    thn_type := thn_t ; Ok (Target.Assign (tmp, thn))))
              in let^ els_stmt =
                process els locals is_mod (fun els ->
                  as_expr els (fun (els, els_t) ->
                    if els_t <> !thn_type
                    then Error "Types of ternary branches must match"
                    else Ok (Target.Assign (tmp, els))))
              in let^ res_k = k (Expr (Variable tmp, !thn_type))
              in Ok (Target.Seq (Contains (elem, thn_stmt, els_stmt), res_k)))
    | ForEachExp (var, lst, body) ->
        process lst locals is_mod (fun lst -> as_expr lst (fun (lst, typ) ->
          match typ with
          | Named (List elem_ty) ->
              let tmp = temp_name ()
              in let res_ty = ref None
              in let fresh_v = fresh_var var
              in let body_env =
                StringMap.add var (LocalVar (fresh_v, elem_ty)) locals
              in let^ body = codegen_stmts body body_env (Some res_ty) is_mod
              in begin match !res_ty with
              | None -> Error "No result type found for for-each expression"
              | Some res_ty ->
                  let^ k_res = k (Expr (Variable tmp, Named (List res_ty)))
                  in Ok (Target.Seq (
                      ForEach (tmp, res_ty, lst, fresh_v, body),
                      k_res))
              end
          | _ -> Error "Can only loop over lists"))

  in process e locals is_mod k

(* codegen_expr takes a continuation which is given an expression (and its
 * type) and produces a statement because some expressions in the Module
 * language require statements in the Calculus and so we need to be able to
 * build statements while comping expressions. *)
let codegen_expr (e : Ast.expr) (types : type_env) (globals : global_env)
  (excepts : Target.typ StringMap.t) (locals : local_env)
  (is_mod : mod_info option)
  (codegen_stmts : Ast.stmt list -> local_env -> Target.typ placeholder option
      -> mod_info option -> (Target.stmt, string) result)
  (k : Target.expr * Target.typ -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  process_expr e types globals excepts locals is_mod codegen_stmts (fun e ->
    as_expr e k)

let codegen_elem (e : Ast.expr) (types : type_env) (globals : global_env)
  (excepts : Target.typ StringMap.t) (locals : local_env)
  (is_mod : mod_info option)
  (codegen_stmts : Ast.stmt list -> local_env -> Target.typ placeholder option
      -> mod_info option -> (Target.stmt, string) result)
  (k : Target.elem -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  process_expr e types globals excepts locals is_mod codegen_stmts (fun e ->
    match e with
    | Elem elem -> k (elem.as_elem None)
    | _ -> Error "Expression is not an element")

let codegen_qual (e : Ast.expr) (types : type_env) (globals : global_env)
  (excepts : Target.typ StringMap.t) (locals : local_env)
  (is_mod : mod_info option)
  (codegen_stmts : Ast.stmt list -> local_env -> Target.typ placeholder option
      -> mod_info option -> (Target.stmt, string) result)
  (k : Target.qual -> (Target.stmt, string) result)
  : (Target.stmt, string) result =
  process_expr e types globals excepts locals is_mod codegen_stmts (fun e ->
    match e with
    | Elem elem -> k (elem.as_qual None)
    | _ -> Error "Expression is not an element")

(* As we process an l-value (the left-hand side of an assignment), at any point
 * what we have processed is either an element (that we'll construct a qual
 * from so we can invoke Add) or a complete l-value (either a variable or an
 * attribute).
 * For l-values we'll produce the type we expect of the value and a function
 * that generates a statement performing the assignment given either the
 * expression to assign or a function which takes the current value (as an
 * expression) and returns the new value.
 *)
type lval_result =
  | Elem of (Target.qual -> (Target.stmt * Target.attr, string) result)
  | LVal of Target.typ
          * ((Target.expr, Target.expr -> Target.expr) Either.t
              -> (Target.stmt, string) result)

let codegen_assignment (lhs : Ast.expr) (types : type_env)
  (globals : global_env) (excepts : Target.typ StringMap.t)
  (locals : local_env) (is_mod : mod_info option)
  (codegen_stmts : Ast.stmt list -> local_env -> Target.typ placeholder option
      -> mod_info option -> (Target.stmt, string) result)
  (rhs : Target.expr) (ty : Target.typ) : (Target.stmt, string) result =

  let rec process_lval (l : Ast.expr) : (lval_result, string) result =
    match l with
    | Id nm ->
        begin match StringMap.find_opt nm locals with
        | Some (LocalVar (v, typ)) ->
            Ok (LVal (typ,
              fun e ->
                match e with
                | Either.Left e -> Ok (Target.Assign (v, e))
                | Either.Right f ->
                    Ok (Target.Assign (v, f (Target.Variable v)))))
        | Some (ModuleVar _) ->
            Error ("Variable " ^ nm ^ " may not be provided")
        | None ->
            match UniqueMap.find nm globals with
            | Some (Attribute (is_local, nm, typ)) ->
                let^ attr = Result.bind (lower_type typ) (fun t -> Ok (nm, t))
                in Ok (LVal (snd attr,
                    fun e ->
                      match e with
                      | Either.Left e ->
                          if is_local
                          then
                            Ok (Target.Add (local_qual (Attribute (attr, e))))
                          else Ok (Target.Add (Attribute (attr, e)))
                      | Either.Right f ->
                          let tmp = temp_name ()
                          in if is_local
                          then Ok (Target.Seq (
                            Target.Get (tmp, local_attr (AttrAccess attr)),
                            Target.Add 
                              (local_qual (Attribute (attr, f (Variable tmp))))
                          ))
                          else Ok (Target.Seq (
                            Target.Get (tmp, AttrAccess attr),
                            Target.Add (Attribute (attr, f (Variable tmp)))))))
            | _ -> Error ("Variable " ^ nm ^ " is undefined")
        end
    | FuncExp (Id elem, args) ->
        begin match UniqueMap.find elem globals with
        | Some (Element (is_local, nm, typ)) ->
            let^ elem = Result.bind (lower_type typ) (fun t -> Ok (nm, t))
            in Ok (Elem (fun q ->
                let attr = ref (Error "Unable to determine attribute")
                in let^ assign =
                  codegen_expr (ProductExp args) types globals excepts locals
                    is_mod codegen_stmts (fun (e, t) ->
                      if t <> snd elem
                      then Error ("Incorrect type for element " ^ nm)
                      else
                        let qual : Target.qual =
                          if is_local
                          then local_qual (Element (elem, e, Some q))
                          else Element (elem, e, Some q)
                        in attr := qual_to_attr qual
                         ; Ok (Target.Add qual))
                in Result.bind (!attr) (fun attr -> Ok (assign, attr))))
        | Some (Uninterpreted (_, _, _)) | Some (Function (_, _, _, _))
            -> Error ("Cannot assign to a function call, " ^ elem
                      ^ " not an element")
        | Some _ -> Error (elem ^ " is not a function")
        | None ->
            let^ _ = Builtins.lookup_builtin elem
            in Error ("Cannot assign to a function call, " ^ elem
                      ^ " not an element")
        end
    | FuncExp (Field (lhs, elem), args) ->
        begin match UniqueMap.find elem globals with
        | Some (Element (_, nm, typ)) ->
            let^ elem = Result.bind (lower_type typ) (fun t -> Ok (nm, t))
            in let^ lhs = process_lval lhs
            in begin match lhs with
            | Elem lhs -> Ok (Elem (fun q ->
                let attr = ref (Error "Unable to determine attribute")
                in let^ assign =
                  codegen_expr (ProductExp args) types globals excepts locals
                    is_mod codegen_stmts (fun (e, t) ->
                      if t <> snd elem
                      then Error ("Incorrect type for element " ^ nm)
                      else
                        let^ (stmt, q) =
                          lhs (Target.Element (elem, e, Some q))
                        in attr := Ok q; Ok stmt)
                in Result.bind (!attr) (fun attr -> Ok (assign, attr))))
            | LVal _ -> Error "Can only access element on an element"
            end
        | Some _ -> Error (elem ^ " is not an element")
        | None -> Error (elem ^ " is not defined")
        end
    | Field (lhs, field) ->
        let^ lhs = process_lval lhs
        in begin match lhs with
        | Elem lhs -> (* We must be accessing an attribute *)
            begin match UniqueMap.find field globals with
            | Some (Attribute (_, nm, typ)) ->
                let^ attr = Result.bind (lower_type typ) (fun t -> Ok (nm, t))
                in Ok (LVal (snd attr,
                    fun e ->
                      match e with
                      | Either.Left e ->
                          let^ (stmt, _) = lhs (Attribute (attr, e)) in Ok stmt
                      | Either.Right f ->
                          let tmp = temp_name ()
                          in let^ (assign, q) =
                            lhs (Attribute (attr, f (Variable tmp)))
                          in Ok (Target.Seq (Get (tmp, q), assign))))
            | Some _ -> Error (field ^ " is not an attribute")
            | None -> Error ("Undefined attribute " ^ field)
            end
        | LVal (ty, lhs) -> (* We must be accessing a record field *)
            (* Modifying a record field always becomes reading the value
             * and writing to a single field *)
            match ty with
            | Struct fields ->
                begin match StringMap.find_opt field fields with
                | Some ty ->
                    Ok (LVal (ty, fun e ->
                      match e with
                      | Either.Left e ->
                          lhs (Either.Right (fun r ->
                            Target.Function (AddField (fields, field),
                              Pair (r, e))))
                      | Either.Right f ->
                          lhs (Either.Right (fun r ->
                            Target.Function (AddField (fields, field),
                              Pair (r, 
                                f (Function (ReadField (fields, field), r))))))))
                | None -> Error ("Record does ont have field " ^ field)
                end
            | _ -> Error "L-value is not a record"
        end
    | ProductField (lhs, idx) ->
        let^ lhs = process_lval lhs
        in begin match lhs with
        | Elem _ -> Error "L-value is not a tuple"
        | LVal (ty, lhs) ->
            let^ (ty, read, update) = construct_product_access ty idx
            in Ok (LVal (ty, fun e ->
              match e with
              | Either.Left e -> lhs (Either.Right (fun p -> update p e))
              | Either.Right f ->
                  lhs (Either.Right (fun p -> update p (f (read p))))))
        end
    | _ -> Error "Invalid l-value"

  in let^ lhs = process_lval lhs
  in match lhs with
  | Elem _ -> Error "Cannot assign to element"
  | LVal (t, f) ->
      if t <> ty
      then Error "Incorrect type in assignment"
      else f (Either.Left rhs)

let codegen_stmts (s : Ast.stmt list) (types : type_env) (globals : global_env)
  (excepts : Target.typ StringMap.t) (locals : local_env) (ret : Target.typ)
  (yield : Target.typ placeholder option) (is_mod : mod_info option)
  (* A terminator to insert at the end of the stmts. *)
  (term : (Target.stmt, string) result) : (Target.stmt, string) result =

  let rec extract_module_args
    (vars : (string * string list * Ast.typ * Ast.expr option) list)
    : ((string * Target.typ) list * (string * Target.typ * Ast.expr) option,
          string) result =
    match vars with
    | [] -> Ok ([], None)
    | (v, _, t, None) :: tl ->
        let^ t = lower_ast_typ t types
        in let^ (vs, default) = extract_module_args tl
        in Ok ((v, t) :: vs, default)
    | (v, _, t, Some d) :: tl ->
        let^ t = lower_ast_typ t types
        in let^ (vs, default) = extract_module_args tl
        in match default with
        | None -> Ok ((v, t) :: vs, Some (v, t, d))
        | Some _ -> Error "multiple default values specified for variable"

  (* Only returns an updated environment and mod_info if the statement after
   * it is reachable (i.e., s is not a terminator or all branches in it have
   * terminators) *)
  in let rec codegen_stmt (s : Ast.stmt) (locals : local_env)
    (yield : Target.typ placeholder option) (is_mod : mod_info option)
    : (Target.stmt * (local_env * mod_info option) option, string) result =
    match s with
    | VarDecls (required, vars) ->
        begin match is_mod with
        | None -> Error "Module-style variable declaration in function"
        | Some (mod_env, input) ->
            let^ (vars, default) = extract_module_args vars
              (* Any declaration with a default is treated as required since it
               * will always have a value *)
            in let decl_info = (required || Option.is_some default,
                                StringSet.of_list (List.map fst vars))
            in let decl_id = uniq ()
            in let new_mod_env = IntMap.add decl_id decl_info mod_env
            in let locals_with_decl =
              List.fold_left (fun env (var, typ) ->
                StringMap.add var (ModuleVar (decl_id, typ)) env)
                locals vars
            in let (new_locals, var_read) =
              update_module_var decl_info input locals_with_decl excepts
            in let^ decl_check =
              match default with
              | None ->
                  Ok (generate_vars_check input vars
                    (if required
                     then fatal ("One of the arguments ["
                                ^ String.concat ", " (List.map fst vars)
                                ^ "] is required") excepts
                    else Pass) excepts)
              | Some (var, typ, value) ->
                  codegen_expr value types globals excepts locals is_mod
                    stmts_expr (fun (value, ty) ->
                      if ty <> typ
                      then Error ("default for " ^ var ^ " has wrong type")
                      else
                        Ok (generate_vars_check input vars
                            (Target.Assign ("#input",
                              Function (AddField (input, var),
                                Pair (Variable "#input",
                                option_some value typ)))) excepts))
            in Ok (Target.Seq (decl_check, var_read),
                    Some (new_locals, Some (new_mod_env, input)))
        end
    | ForLoop (v, l, b) ->
        let^ loop =
          codegen_expr l types globals excepts locals is_mod stmts_expr
          (fun (lst, typ) ->
            match typ with
            | Named (List t) ->
                let fresh_v = fresh_var v
                in let body_env = StringMap.add v (LocalVar (fresh_v, t)) locals
                in Result.bind (codegen_stmts b body_env None is_mod)
                  (fun (b, _) ->
                    Ok (Target.ForEach ("_", Primitive Unit, lst, fresh_v, b)))
          | _ -> Error "Can only loop over lists")
        in Ok (loop, Some (locals, is_mod))
    | IfProvided (var, thn, els) ->
        begin match is_mod with
        | None -> Error "Module-style variable check in function"
        | Some (mod_env, input) ->
            match StringMap.find_opt var locals with
            | Some (LocalVar _) ->
                Error ("Variable " ^ var ^ " is a local, not a module variable")
            | None ->
                Error ("Variable " ^ var ^ " is undefined")
            | Some (ModuleVar (mod_id, typ)) ->
                let (required, options) = IntMap.find mod_id mod_env
                in let fresh_nm = fresh_var var
                in let false_decl_info =
                  (required, StringSet.remove var options)
                in let false_mod_env =
                  IntMap.add mod_id false_decl_info mod_env
                in let (false_locals, false_start) =
                  update_module_var false_decl_info input
                    (StringMap.remove var locals) excepts
                in let true_locals =
                  select_module_var var mod_id options fresh_nm typ locals
                in let^ (thn, thn_reach) =
                  codegen_stmts thn true_locals yield is_mod
                in let^ (els, els_reach) =
                  codegen_stmts els false_locals yield
                    (Some (false_mod_env, input))
                in Ok (Target.Match (
                        Function (ReadField (input, var), Variable "#input"),
                        fresh_nm,
                        Seq (false_start, els), (* None *)
                        thn (* Some *)
                    ), if not thn_reach && not els_reach
                        then None
                        else Some (locals, is_mod))
        end
    | IfExists (q, thn, els) ->
        let reachable = ref false
        in let^ res =
          codegen_elem q types globals excepts locals is_mod stmts_expr
          (fun elem ->
            let^ (thn, thn_reach) = codegen_stmts thn locals yield is_mod
            in let^ (els, els_reach) = codegen_stmts els locals yield is_mod
            in reachable := thn_reach || els_reach
            ; Ok (Target.Contains (elem, thn, els)))
        in Ok (res, if not !reachable then None else Some (locals, is_mod))
    | IfThenElse (c, thn, els) ->
        let reachable = ref false
        in let^ res =
          codegen_expr c types globals excepts locals is_mod stmts_expr
          (fun (c, typ) ->
            if typ <> Primitive Bool
            then Error "Condition must be a boolean value"
            else
              let^ (thn, thn_reach) = codegen_stmts thn locals yield is_mod
              in let^ (els, els_reach) = codegen_stmts els locals yield is_mod
              in reachable := thn_reach || els_reach
              ; Ok (Target.Cond (c, thn, els)))
        in Ok (res, if not !reachable then None else Some (locals, is_mod))
    | Match (e, cs) ->
        (* First, we need to identify the type that we are matching over.
         * We look at the first case for this, if there are none the match
         * compiles into just evaluating the expression *)
        begin match cs with
        | [] ->
            let^ res =
              codegen_expr e types globals excepts locals is_mod stmts_expr
                (fun _ -> Ok Pass)
            in Ok (res, Some (locals, is_mod))
        | ((type_name, type_arg, _, _), _) :: _ ->
            let^ constructors = lookup_enum types type_name type_arg
            in let cases =
              Array.make (StringMap.cardinal constructors) None
            in let reachable = ref false
            in let^ () =
              List.fold_left
                (fun i ((typ, ty_arg, cons, vars), body) ->
                  Result.bind i (fun () ->
                    if typ <> type_name || ty_arg <> type_arg
                    then Error "Mismatched types in match case"
                    else
                      match StringMap.find_opt cons constructors with
                      | None ->
                          Error ("No constructor " ^ cons ^ " for type " ^ typ)
                      | Some (pos, args) ->
                          match cases.(pos) with
                          | Some _ ->
                              Error ("Duplicate case " ^ cons ^ " in match")
                          | None ->
                              let^ typ = lower_types args
                              in let^ (setup, case_env) =
                                generate_var_inits vars typ
                                  (Variable "#match") locals
                              in let^ (body, body_reach) =
                                codegen_stmts body case_env yield is_mod
                              in reachable := !reachable || body_reach
                              ; Ok ( cases.(pos) <-
                                      Some (Target.Seq (setup, body)) )))
                (Ok ()) cs
            in let^ res =
              codegen_expr e types globals excepts locals is_mod stmts_expr
              (fun (e, t) ->
                if pattern_type_matches types (type_name, type_arg) t
                then
                  Ok (Target.Seq (
                    Target.Assign ("#match", e),
                    array_foldr1 cases
                      (fun case ->
                        match case with
                        | None -> reachable := true; Target.Pass
                        | Some s -> s)
                      (fun l r ->
                        Target.Match (Variable "#match", "#match", l, r))
                  ))
                else Error "Incorrect type of scrutinee")
            in Ok (res, if not !reachable then None else Some (locals, is_mod))
        end
    | Clear e ->
        let^ res =
          codegen_qual e types globals excepts locals is_mod stmts_expr
          (fun q ->
            let^ nq = negate_qual q
            in Ok (Target.Add nq))
        in Ok (res, Some (locals, is_mod))
    | Touch e ->
        let^ res =
          codegen_qual e types globals excepts locals is_mod stmts_expr
            (fun q -> Ok (Target.Add q))
        in Ok (res, Some (locals, is_mod))
    | Assert e ->
        let^ result =
          codegen_expr e types globals excepts locals is_mod stmts_expr
          (fun (e, t) ->
            if t <> Primitive Bool
            then Error "Condition must be a boolean value"
            else
              Ok (Target.Cond (e, Pass, fatal "assertion failed" excepts)))
        in Ok (result, Some (locals, is_mod))
    | AssertExists q ->
        let^ result =
          codegen_elem q types globals excepts locals is_mod stmts_expr
          (fun elem ->
            Ok (Target.Contains (elem, Pass, fatal "assertion failed" excepts)))
        in Ok (result, Some (locals, is_mod))
    | Return e ->
        let^ result =
          codegen_expr e types globals excepts locals is_mod stmts_expr
          (fun (e, t) ->
            if t <> ret
            then Error "Mismatch in return type"
            else Ok (Target.Return e))
        in Ok (result, None)
    | Yield e ->
        begin match yield with
        | None -> Error "Yield not allowed in this context"
        | Some ty ->
            let^ result =
              codegen_expr e types globals excepts locals is_mod stmts_expr
              (fun (e, t) ->
                match !ty with
                | None -> ty := Some t; Ok (Target.Yield e)
                | Some ty ->
                    if t <> ty
                    then Error "Mismatch in yield type"
                    else Ok (Target.Yield e))
            in Ok (result, None)
        end
    | LetStmt (var, exp) ->
        let fresh_var = fresh_var var
        in let ty = ref (Target.Primitive Unit)
        in let^ result =
          codegen_expr exp types globals excepts locals is_mod stmts_expr
          (fun (e, t) ->
            ty := t; Ok (Target.Assign (fresh_var, e)))
        in let new_locals =
          StringMap.add var (LocalVar (fresh_var, !ty)) locals
        in Ok (result, Some (new_locals, is_mod))
    | Assign (lhs, rhs) ->
        let^ result =
          codegen_expr rhs types globals excepts locals is_mod stmts_expr
          (fun (e, t) ->
            codegen_assignment lhs types globals excepts locals is_mod
              stmts_expr e t)
        in Ok (result, Some (locals, is_mod))
    | Raise (nm, exc) ->
        let^ exc_typ =
          match StringMap.find_opt nm excepts with
          | None -> Error ("Undefined exception " ^ nm)
          | Some t -> Ok t
        in let^ result =
          codegen_expr exc types globals excepts locals is_mod stmts_expr
          (fun (e, t) ->
            if t <> exc_typ
            then Error ("Incorrect type for exception " ^ nm)
            else Ok (raise nm e excepts))
        in Ok (result, None)
    | TryCatch (body, catch, finally) ->
        let^ (body, body_reach) = codegen_stmts body locals yield is_mod
        in let^ (catch, catch_reach) =
          match catch with
          | None -> Ok (Target.Raise (Variable "#catch"), true)
          | Some (exc, vars, catch) ->
              match StringMap.find_opt exc excepts with
              | None -> Error ("Undefined exception " ^ exc)
              | Some typ ->
                  let^ (setup, body_locals) =
                    generate_var_inits vars typ (Variable "#except") locals
                  in let^ (catch, catch_reach) =
                    codegen_stmts catch body_locals yield is_mod
                  in Ok (
                    Target.Match (
                      Function (UnpackExcept (excepts, exc), Variable "#catch"),
                      "#except",
                      (* None, some other error *)
                      Raise (Variable "#catch"),
                      (* Some, this kind of error *)
                      Seq (setup, catch)),
                    catch_reach)
        in let^ (finally, finally_reach) =
          codegen_stmts finally locals yield is_mod
        in Ok (Target.TryCatch (body, "#catch", catch, finally),
            (* If the finally block always hits a terminator, the statement
             * after the try-catch will never be reached. Otherwise, we only
             * do not reach the statement after if the body always hits a
             * terminator and the catch always hits one (since the body's
             * terminator might be a raise that is caught by the body) *)
            if not finally_reach || (not body_reach && not catch_reach)
            then None
            else Some (locals, is_mod))
    | Localize body ->
        let^ (body, body_reach) = codegen_stmts body locals yield is_mod
        in Ok (Target.Localize 
                (("#local", Primitive Unit), Literal (Unit ()), body),
               if body_reach then Some (locals, is_mod) else None)

  (* The returned bool indicates whether control can continue after this list *)
  and codegen_stmts (s : Ast.stmt list) (locals : local_env)
    (yield : Target.typ placeholder option) (is_mod : mod_info option)
    : (Target.stmt * bool, string) result =
    match s with
    | [] -> Ok (Pass, true)
    | s :: tl ->
        let^ (res_s, after) = codegen_stmt s locals yield is_mod
        in match after with
        | None ->
            begin match tl with
            | [] -> Ok (res_s, false)
            | _ :: _ -> Error "Unreachable code"
            end
        | Some (new_locals, new_mod) ->
            let^ (res_tl, res_reach) =
              codegen_stmts tl new_locals yield new_mod
            in Ok (Target.Seq (res_s, res_tl), res_reach)

  and stmts_expr (s : Ast.stmt list) (locals : local_env)
    (yield : Target.typ placeholder option) (is_mod : mod_info option)
    : (Target.stmt, string) result =
    let^ (res, _) = codegen_stmts s locals yield is_mod
    in Ok res

  in let^ (res, reach_end) = codegen_stmts s locals yield is_mod
  in if not reach_end
    then Ok res
    else Result.bind term (fun t -> Ok (Target.Seq (res, t)))

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
    | Attribute (is_local, nm, ty) ->
        Result.bind (process_type ty types) (fun typ ->
          UniqueMap.add nm (Attribute (is_local, nm, typ)) globals)
    | Element (is_local, nm, ty) ->
        Result.bind (process_type ty types) (fun typ ->
          UniqueMap.add nm (Element (is_local, nm, typ)) globals)
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

  in let codegen_func (excepts : Target.typ StringMap.t) f
    : (unit, string) result =
    match f with
    | None -> Ok ()
    (* Function body *)
    | Some (Either.Left (body, args, arg_ty), ret_type, body_ref) ->
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error "Reached end of function without return"
        (* Because the calculus only allows a single arguments for everything,
         * we generate code that reads each argument out of the initial tuple
         * passed in as the #input argument *)
        in let^ (setup, locals) =
          generate_var_inits args arg_ty (Variable "#input") empty_local_env
        in let^ ret_type = lower_type ret_type
        in let^ func_body =
          codegen_stmts body types globals excepts locals ret_type None
            None default_ret
        in Ok (body_ref := Some (Target.Seq (setup, func_body)))
    (* Module body *)
    | Some (Either.Right (body, input), ret_type, body_ref) ->
        let default_ret : (Target.stmt, string) result =
          if type_equality ret_type Unit
          then Ok (Return (Literal (Unit ())))
          else Error "Reached end of module without return"
        in let^ ret_type = lower_type ret_type
        in let^ input_type = smap_map_res lower_type input
        in let^ func_body =
          codegen_stmts body types globals excepts empty_local_env ret_type
            None (Some (empty_mod_env, input_type)) default_ret
        in Ok (body_ref := Some (func_body))

  in let^ () = foreachs_res parsed add_type
  in let^ () = foreachs_res parsed add_def
  in let^ funcs = flatmap_res add_func parsed
  in let^ excepts =
    UniqueMap.fold (fun e t excepts -> Result.bind excepts (fun excepts ->
      let^ typ = lower_type t
      in Ok (StringMap.add e typ excepts)))
      excepts
      (Ok (StringMap.singleton "!FATAL" (Target.Primitive String)))
  in let^ () = foreach_res funcs (codegen_func excepts)
  in Ok { types = types; globals = globals; excepts = excepts }

(* Code-gen entry for an individual program given an existing context *)
let codegen_program (body : Ast.stmt list) (c : context)
  : (Target.stmt, string) result =
  let^ res =
    codegen_stmts body c.types c.globals c.excepts empty_local_env
      (Primitive Unit) None None (Ok (Return (Literal (Unit ()))))
  (* We insert a requirement that #local() exist since this is an element
   * used by our compilation process and not having it exist can be a problem
   * if we write a local before reading any. *)
  in Ok (Target.Seq (
      Contains (Element (("#local", Primitive Unit), Literal (Unit ())),
        Pass,
        fatal "assertion failed" c.excepts),
      res))

let find_module_def (name : string list) (ctx : context) : module_info option =
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
  in helper name (Environment ctx.globals)

let find_function_body (name : string list) (c : context)
  : (Target.stmt, string) result =
  let rec helper name entry =
    match name with
    | [] ->
        begin match entry with
        | Module m ->
            begin match !(m.body) with
            | None -> Error "No body for module"
            | Some s -> Ok s
            end
        | Function (_, _, _, s) ->
            begin match !s with
            | None -> Error "No body for function"
            | Some s -> Ok s
            end
        | _ -> Error "Not a function"
        end
    | nm :: name ->
        match entry with
        | Environment env ->
            begin match UniqueMap.find nm env with
            | None -> Error "No such function"
            | Some entry -> helper name entry
            end
        | _ -> Error "Not a function"
  in helper name (Environment c.globals)
