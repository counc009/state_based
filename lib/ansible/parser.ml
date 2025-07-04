(* Note: even though the YAML spec requires that maps have unique labels, the
 * OCaml YAML library does not seem to enforce this, so our handling of
 * playbooks and tasks handles and reports errors if a field is set multiple
 * times *)

module Jinterp = Jingoo.Jg_interp
module Jtypes = Jingoo.Jg_types

type unary  = Not | Lower
type binary = Concat | Equals | And | Or

type value =
  | String of string
  | Int    of int
  | Float  of float
  | Bool   of bool
  | List   of value list
  | Ident  of string
  | Unary  of value * unary
  | Binary of value * binary * value
  | Dot    of value * string

type mod_use = {
  mod_name: string;
  args: (string * value) list
}

class mod_result name =
  object
    val args           = (Hashtbl.create 10 : (string, value) Hashtbl.t)

    val mutable errors = ([] : string list)

    method add_arg nm v =
      if Hashtbl.mem args nm
      then errors <- Printf.sprintf "Argument %s appears multiple times" nm
                  :: errors
      else
        Hashtbl.add args nm v

    method to_mod =
      if not (List.is_empty errors)
      then Error errors
      else Ok { mod_name = name; args = List.of_seq (Hashtbl.to_seq args) }
  end

type loop_kind =
  | ItemLoop of value
  | FileGlob of value

type task = {
  name: string;
  register: string;
  ignore_errors: bool;
  condition: value option;
  loop: loop_kind option;
  module_invoke: mod_use;
  become: bool;
  notify: string list
}

class task_result =
  object
    val mutable name          = (None : string option)
    val mutable register      = (None : string option)
    val mutable ignore_errors = (None : bool option)
    val mutable condition     = (None : value option)
    val mutable loop          = (None : loop_kind option)
    val mutable module_invoke = (None : mod_use option)

    val mutable notify        = (None : string list option)
    val mutable become        = (None : bool option)

    val mutable errors        = ([] : string list)

    method add_name nm =
      match name with
      | None -> name <- Some nm
      | _    -> errors <- "Multiple name fields" :: errors
    method add_register nm =
      match register with
      | None -> register <- Some nm
      | _    -> errors <- "Multiple register fields" :: errors
    method add_ignore_errors v =
      match ignore_errors with
      | None -> ignore_errors <- Some v
      | _    -> errors <- "Multiple ignore_errors fields" :: errors
    method add_when v =
      match condition with
      | None -> condition <- Some v
      | _    -> errors <- "Multiple when fields" :: errors
    method add_loop l =
      match loop with
      | None -> loop <- Some l
      | _    -> errors <- "Multiple looping fields" :: errors
    method add_module m =
      match module_invoke with
      | None   -> module_invoke <- Some m
      | Some c -> errors <-
        Printf.sprintf "Multiple modules specified: %s and %s" c.mod_name m.mod_name
        :: errors

    method add_notify hs =
      match notify with
      | None -> notify <- Some hs
      | _    -> errors <- "Multiple notify fields" :: errors

    method add_become b =
      match become with
      | None -> become <- Some b
      | _    -> errors <- "Multiple become fields" :: errors

    method to_task =
      if not (List.is_empty errors)
      then Error errors
      else
        match module_invoke with
        | None -> Error ["no module invocation in task"]
        | Some m ->
            Ok { name          = Option.value name ~default:""
               ; register      = Option.value register ~default:"_"
               ; ignore_errors = Option.value ignore_errors ~default:false
               ; condition     = condition
               ; loop          = loop
               ; module_invoke = m
               ; notify        = Option.value notify ~default:[]
               ; become        = Option.value become ~default:false }
  end

type handler = {
  name: string;
  listen: string;
  register: string;
  ignore_errors: bool;
  condition: value option;
  loop: loop_kind option;
  module_invoke: mod_use;
  become: bool;
}

class handler_result =
  object
    val mutable name          = (None : string option)
    val mutable listen        = (None : string option)
    val mutable register      = (None : string option)
    val mutable module_invoke = (None : mod_use option)

    val mutable ignore_errors = (None : bool option)
    val mutable condition     = (None : value option)
    val mutable loop          = (None : loop_kind option)
    val mutable become        = (None : bool option)

    val mutable errors        = ([] : string list)

    method add_name nm =
      match name with
      | None -> name <- Some nm
      | _    -> errors <- "Multiple name fields" :: errors
    method add_listen nm =
      match listen with
      | None -> listen <- Some nm
      | _    -> errors <- "Multiple listen fields" :: errors
    method add_module m =
      match module_invoke with
      | None   -> module_invoke <- Some m
      | Some c -> errors <-
        Printf.sprintf "Multiple modules specified: %s and %s" c.mod_name m.mod_name
        :: errors

    method add_register nm =
      match register with
      | None -> register <- Some nm
      | _    -> errors <- "Multiple register fields" :: errors
    method add_ignore_errors v =
      match ignore_errors with
      | None -> ignore_errors <- Some v
      | _    -> errors <- "Multiple ignore_errors fields" :: errors
    method add_when v =
      match condition with
      | None -> condition <- Some v
      | _    -> errors <- "Multiple when fields" :: errors
    method add_loop l =
      match loop with
      | None -> loop <- Some l
      | _    -> errors <- "Multiple looping fields" :: errors
    method add_become b =
      match become with
      | None -> become <- Some b
      | _    -> errors <- "Multiple become fields" :: errors

    method to_handler =
      if not (List.is_empty errors)
      then Error errors
      else
        match module_invoke with
        | None -> Error ["no module invocation in handler"]
        | Some m ->
            match name with
            | None -> Error ["no name field for handler"]
            | Some n ->
                Ok { name          = n
                   ; listen        = Option.value listen ~default:n
                   ; register      = Option.value register ~default:""
                   ; ignore_errors = Option.value ignore_errors ~default:false
                   ; condition     = condition
                   ; loop          = loop
                   ; module_invoke = m
                   ; become        = Option.value become ~default:false }
  end

type play = {
  name        : string;
  hosts       : string option;
  remote_user : string;
  is_root     : bool option;
  become      : bool;
  tasks       : task list;
  handlers    : handler list;
}

class play_result =
  object
    val mutable name        = (None : string option)
    val mutable hosts       = (None : string option)
    val mutable remote_user = (None : string option)
    val mutable tasks       = (None : task list option)
    val mutable handlers    = (None : handler list option)

    val mutable become      = (None : bool option)

    val mutable errors      = ([] : string list)

    method add_name nm =
      match name with
      | None -> name <- Some nm
      | _    -> errors <- "Multiple name fields" :: errors
    method add_hosts h =
      match hosts with
      | None -> hosts <- Some h
      | _    -> errors <- "Multiple hosts fields" :: errors
    method add_remote_user n =
      match remote_user with
      | None -> remote_user <- Some n
      | _    -> errors <- "Multiple remote_user fields" :: errors
    method add_tasks ts =
      match tasks with
      | None -> tasks <- Some ts
      | _    -> errors <- "Multiple tasks fields" :: errors
    method add_handlers hs =
      match handlers with
      | None -> handlers <- Some hs
      | _    -> errors <- "Multiple handlers fields" :: errors

    method add_become b =
      match become with
      | None -> become <- Some b
      | _    -> errors <- "Multiple become fields" :: errors

    method to_play =
      if not (List.is_empty errors)
      then Error errors
      else
        match tasks with
        | None -> Error ["no tasks in play"]
        | Some t ->
            Ok { name         = Option.value name ~default:""
               ; hosts        = hosts
              (* Per https://docs.ansible.com/ansible/latest/inventory_guide/connection_details.html#setting-a-remote-user
               * the default for the user is the name of the local user *)
               ; remote_user  = Option.value remote_user ~default:"#local_user"
               ; is_root      = Option.map (fun nm -> nm = "root") remote_user
               ; become       = Option.value become ~default:false
               ; tasks        = t
               ; handlers     = Option.value handlers ~default:[] }
  end

let rec jinja_to_value (j: Jtypes.ast) : (value, string) result =
  let rec jlit_to_value (j: Jtypes.tvalue) : (value, string) result =
    match j with
    | Tnull -> Ok (String "")
    | Tint i -> Ok (Int i)
    | Tbool b -> Ok (Bool b)
    | Tfloat f -> Ok (Float f)
    | Tstr s -> Ok (String s)
    | Tlist xs -> Result.map (fun xs -> List xs)
      (List.fold_right
        (fun x xs ->
          Result.bind (jlit_to_value x)
            (fun x -> Result.bind xs (fun xs -> Ok (x :: xs))))
        xs
        (Ok []))
    | _ -> Error "Unsupported Jinja literal value"
  in let rec jexpr_to_value (j: Jtypes.expression) : (value, string) result =
    match j with
    | IdentExpr nm -> Ok (Ident nm)
    | LiteralExpr v -> jlit_to_value v
    | NotOpExpr e -> Result.map (fun v -> Unary (v, Not)) (jexpr_to_value e)
    | AndOpExpr (lhs, rhs) -> Result.bind (jexpr_to_value lhs)
        (fun lhs -> Result.bind (jexpr_to_value rhs)
          (fun rhs -> Ok (Binary (lhs, And, rhs))))
    | OrOpExpr (lhs, rhs) -> Result.bind (jexpr_to_value lhs)
        (fun lhs -> Result.bind (jexpr_to_value rhs)
          (fun rhs -> Ok (Binary (lhs, Or, rhs))))
    | EqEqOpExpr (lhs, rhs) -> Result.bind (jexpr_to_value lhs)
        (fun lhs -> Result.bind (jexpr_to_value rhs)
          (fun rhs -> Ok (Binary (lhs, Equals, rhs))))
    | NotEqOpExpr (lhs, rhs) -> Result.bind (jexpr_to_value lhs)
        (fun lhs -> Result.bind (jexpr_to_value rhs)
          (fun rhs -> Ok (Unary (Binary (lhs, Equals, rhs), Not))))
    | DotExpr (ex, field) -> Result.bind (jexpr_to_value ex)
        (fun ex -> Ok (Dot (ex, field)))
    | ApplyExpr (IdentExpr "lower", [(None, arg)]) ->
        Result.bind (jexpr_to_value arg) (fun ex -> Ok (Unary (ex, Lower)))
    | _ -> Error "unhandled Jinja expression form"
  in let jstmt_to_value (j: Jtypes.statement) : (value, string) result =
    match j with
    | TextStatement s -> Ok (String s)
    | ExpandStatement e -> jexpr_to_value e
    | _ -> Error "Unsupported Jinja form"
  in match j with
  | [] -> Ok (String "")
  | [e] -> jstmt_to_value e
  | e :: js -> Result.bind (jstmt_to_value e)
      (fun hd -> Result.bind (jinja_to_value js)
        (fun tl -> Ok (Binary (hd, Concat, tl))))

type var_typ = Unknown of string * Modules.Ast.typ (* name of the variable and a suggested type *)
             | Concrete of Modules.Ast.typ
type play_env = (string, var_typ) Hashtbl.t

let list_to_and (v: value) : value =
  match v with
  | List [] -> Bool true
  | List [v] -> v
  | List (v::vs) -> List.fold_right (fun x y -> Binary (x, And, y)) vs v
  | _ -> v

let rec codegen_type_to_ast_typ (t: Modules.Codegen.typ) : Modules.Ast.typ =
  match t with
  | Bool -> Bool
  | Int -> Int
  | Float -> Float
  | String -> String
  | Path -> Path
  | Unit -> Unit
  | Option t -> Option (codegen_type_to_ast_typ t)
  | List t -> List (codegen_type_to_ast_typ t)
  | Product ts -> Product (List.map codegen_type_to_ast_typ ts)
  | Struct (nm, _) | Enum (nm, _) -> Named nm
  | Placeholder { contents = Some t } -> codegen_type_to_ast_typ t
  | Placeholder { contents = None } -> failwith "Internal Error: unresolved placeholder"

let singleton_list (elemTy: Modules.Ast.typ) (elem: Modules.Ast.expr) =
  Modules.Ast.EnumExp (Id "list", Some elemTy, "cons",
    [ elem; Modules.Ast.EnumExp (Id "list", Some elemTy, "nil", []) ])

let process_ansible (file: string) (tys : Modules.Codegen.type_env)
  (env : Modules.Codegen.global_env) : (Modules.Ast.stmt list, string) result =
  let process_string v =
    match v with
    | `String s -> Ok s
    | `Bool   b -> Ok (string_of_bool b)
    | `Float  f -> Ok (string_of_float f)
    | `Null     -> Ok "" (* It seems null is sometimes used as an empty string *)
    | `A _      -> Error "expected string, found sequence"
    | `O _      -> Error "expected string, found mapping"
  in let process_bool v =
    match v with
    | `Bool b -> Ok b
    | _       -> Error "expected a bool"
  in let process_string_list v =
    match v with
    | `String s -> Ok [s]
    | `Bool   b -> Ok [string_of_bool b]
    | `Float  f -> Ok [string_of_float f]
    | `Null     -> Ok []
    | `A vs     -> List.fold_right 
        (fun v res -> Result.bind res (fun res ->
          Result.bind (process_string v) (fun v -> Ok (v :: res)))
        ) vs (Ok [])
    | `O _      -> Error "expected string list, found mapping"
  in let rec process_value v =
    match v with
    | `Null     -> Ok (String "")
    | `Bool b   -> Ok (Bool b)
    | `Float f  -> Ok (Float f)
    | `String s -> jinja_to_value (Jinterp.ast_from_string s)
    | `A vs     ->
        let rec process vs =
          match vs with
          | [] -> Ok []
          | hd :: tl ->
              Result.bind (process_value hd)
                (fun h -> Result.map (fun tl -> h :: tl) (process tl))
        in Result.map (fun vs -> List vs) (process vs)
    | `O _      -> Error "expected value found mapping"
  in let rec process_condition v =
    match v with
    | `Null -> Ok (Bool true)
    | `Bool b -> Ok (Bool b)
    | `Float f -> Ok (Float f)
    | `String s ->
        jinja_to_value (Jinterp.ast_from_string (Printf.sprintf "{{ %s }}" s))
    | `A vs ->
        let rec process vs =
          match vs with
          | [] -> Ok []
          | hd :: tl ->
              Result.bind (process_condition hd)
                (fun h -> Result.map (fun tl -> h :: tl) (process tl))
        in Result.map (fun vs -> List vs) (process vs)
    | `O _ -> Error "expected conditions, found mapping"
  in let rec codegen_value v (t : Modules.Ast.typ option) (play_env: play_env)
    : (Modules.Ast.expr * Modules.Ast.typ, string) result =
    match v with
    | Int i ->
        begin match t with
        | None -> Ok (Modules.Ast.IntLit i, Modules.Ast.Int)
        | Some Int -> Ok (Modules.Ast.IntLit i, Modules.Ast.Int)
        | Some Float -> Ok (Modules.Ast.FloatLit (float_of_int i), Modules.Ast.Float)
        | Some String -> Ok (Modules.Ast.StringLit (string_of_int i), Modules.Ast.String)
        | Some (List t) ->
            Result.map (fun (e, t) -> (singleton_list t e, Modules.Ast.List t))
              (codegen_value v (Some t) play_env)
        | _ -> Error "Incorrect type, found integer"
        end
    | Float f ->
        begin match t with
        | None -> Ok (Modules.Ast.FloatLit f, Modules.Ast.Float)
        | Some Int ->
            if Float.is_integer f
            then Ok (Modules.Ast.IntLit (Float.to_int f), Modules.Ast.Int)
            else Error (Printf.sprintf "Expected integer found float '%f'" f)
        | Some Float -> Ok (Modules.Ast.FloatLit f, Modules.Ast.Float)
        | Some String -> Ok (Modules.Ast.StringLit (string_of_float f), Modules.Ast.String)
        | Some (List t) ->
            Result.map (fun (e, t) -> (singleton_list t e, Modules.Ast.List t))
              (codegen_value v (Some t) play_env)
        | _ -> Error ("Incorrect type, found number")
        end
    | Bool b ->
        begin match t with
        | None -> Ok (Modules.Ast.BoolLit b, Modules.Ast.Bool)
        | Some Bool -> Ok (Modules.Ast.BoolLit b, Modules.Ast.Bool)
        | Some String -> Ok (Modules.Ast.StringLit (string_of_bool b), Modules.Ast.String)
        | Some (List t) ->
            Result.map (fun (e, t) -> (singleton_list t e, Modules.Ast.List t))
              (codegen_value v (Some t) play_env)
        | _ -> Error ("Incorrect type, found bool")
        end
    | List vs ->
        (* We construct a list as a series of cons *)
        begin match t with
        | None ->
            let vals =
              List.fold_right
                (fun v tl_info ->
                  Result.bind tl_info
                    (fun (tl, el) ->
                      Result.map (fun (v, t) -> (v :: tl, Some t))
                        (codegen_value v el play_env)))
                vs
                (Ok ([], None))
            in Result.bind vals
              (fun (vals, elem_typ) ->
                match elem_typ with
                | None -> Error "could not determine the type of a list"
                | Some el ->
                    Ok (List.fold_right
                      (fun v e ->
                        Modules.Ast.EnumExp (
                          Id "list",
                          Some el,
                          "cons",
                          [v; e]))
                      vals
                      (Modules.Ast.EnumExp (Id "list", Some el, "nil", [])),
                      Modules.Ast.List el))
        | Some (List el) ->
            let vals =
              let rec process_vals vs =
                match vs with
                | [] -> Ok []
                | v :: vs ->
                    match codegen_value v (Some el) play_env with
                    | Ok (v, _) ->
                        Result.map (fun tl -> v :: tl) (process_vals vs)
                    | Error msg -> Error msg
              in process_vals vs
            in Result.map
                (fun vals ->
                  (List.fold_right
                    (fun v e ->
                      Modules.Ast.EnumExp (
                        Id "list",
                        Some el,
                        "cons",
                        [v; e]))
                    vals
                    (* Nil list *)
                    (Modules.Ast.EnumExp (Id "list", Some el, "nil", [])),
                    Modules.Ast.List el))
                vals
        | _ -> Error ("Incorrect type, found list")
        end
    | String s ->
        (* Strings in YAML can actually represent many things in our type-system,
         * specifically strings, paths, and enum values *)
        begin match t with
        | None -> Ok (StringLit s, Modules.Ast.String)
        | Some String -> Ok (StringLit s, Modules.Ast.String)
        | Some Path   -> Ok (PathLit s, Modules.Ast.Path)
        | Some (Named nm) ->
            begin match Modules.Codegen.UniqueMap.find nm tys with
            | None -> Error "Internal Error: type undefined"
            | Some typ ->
                let rec process_for_type (typ : Modules.Codegen.typ)
                  : (Modules.Ast.expr * Modules.Ast.typ, string) result =
                  match typ with
                  | String -> Ok (StringLit s, Named nm)
                  | Path   -> Ok (PathLit s, Named nm)
                  | Placeholder { contents = Some typ } -> process_for_type typ
                  | Placeholder { contents = None } -> Error ("Internal Error: unknown placeholder")
                  | Enum (_, constructors) ->
                      begin match Modules.Codegen.StringMap.find_opt s constructors with
                      | None -> Error (Printf.sprintf
                          "Invalid value '%s' expected one of [%s]"
                          s
                          (String.concat ", "
                            (List.map fst
                              (Modules.Codegen.StringMap.bindings constructors))))
                      | Some (_, []) -> Ok(EnumExp (Id nm, None, s, []), Named nm)
                      | Some (_, _) -> Error (Printf.sprintf
                          "Constructor %s cannot be used from Ansible, has argument"
                          s)
                      end
                  | _ -> Error ("Incorrect type, found string-like")
                in process_for_type typ
            end
        | Some (List t) ->
            Result.map (fun (e, t) -> (singleton_list t e, Modules.Ast.List t))
              (codegen_value v (Some t) play_env)
        | _ -> Error ("Incorrect type, found string-like")
        end
    | Ident nm ->
        begin match Hashtbl.find_opt play_env nm, t with
        | Some (Concrete ty), Some t when t = ty -> Ok (Modules.Ast.Id nm, t)
        | Some (Concrete String), Some Path ->
            Ok (Modules.Ast.FuncExp (Id "path_of_string", [Modules.Ast.Id nm]),
                Path)
        | Some (Concrete Path), Some String ->
            Ok (Modules.Ast.FuncExp (Id "string_of_path", [Modules.Ast.Id nm]),
                String)
        | Some (Concrete _), Some _ -> Error "mismatched types"
        | Some (Concrete ty), None -> Ok (Modules.Ast.Id nm, ty)
        | Some (Unknown (_, _)), Some t ->
            let () = Hashtbl.add play_env nm (Concrete t)
            in Ok (Modules.Ast.Id nm, t)
        | Some (Unknown (_, t)), None ->
            let () = Hashtbl.add play_env nm (Concrete t)
            in Ok (Modules.Ast.Id nm, t)
        | None, _ ->
            (* See if this is a built-in variable *)
            match nm with
            | "ansible_os_family" ->
                begin match t with
                | Some String | None ->
                    (* env().os_family *)
                    Ok (Field (FuncExp (Id "env", []), "os_family"), String)
                | _ -> Error "mismatched types"
                end
            | "ansible_distribution" ->
                begin match t with
                | Some String | None ->
                    (* env().os_distribution *)
                    Ok (Field (FuncExp (Id "env", []), "os_distribution"), String)
                | _ -> Error "mismatched types"
                end
            | "ansible_user_id" ->
                begin match t with
                | Some String | None ->
                    (* env().active_user *)
                    Ok (Field (FuncExp (Id "env", []), "active_user"), String)
                | _ -> Error "mismatched types"
                end
            | "ansible_user_gid" ->
                (* TODO: This seems to actually generate the group id not name *)
                begin match t with
                | Some String | None ->
                    (* env().active_group *)
                    Ok (Field (FuncExp (Id "env", []), "active_group"), String)
                | _ -> Error "mismatched types"
                end
            | _ -> Error ("Unknown variable " ^ nm)
        end
    | Unary (v, op) ->
        begin match op, t with
        | Not, Some Bool | Not, None ->
            Result.bind (codegen_value v (Some Bool) play_env)
              (fun (v, _) -> Ok (Modules.Ast.UnaryExp (v, Not),
                                 Modules.Ast.Bool))
        | Not, _ -> Error "Incorrect type for not (productes boolean)"
        | Lower, Some String | Lower, None ->
            Result.bind (codegen_value v (Some String) play_env)
              (fun (v, _) -> Ok (Modules.Ast.FuncExp (Id "to_lower", [v]),
                                 Modules.Ast.String))
        | Lower, Some Path ->
            Result.bind (codegen_value v (Some String) play_env)
              (fun (v, _) -> Ok (Modules.Ast.FuncExp (Id "path_of_string",
                [FuncExp (Id "to_lower", [v])]), Modules.Ast.Path))
        | Lower, _ -> Error "Incorrect type for lower (productes string)"
        end
    | Binary (lhs, op, rhs) ->
        let op_info : (Modules.Ast.typ option
                    * (Modules.Ast.typ -> Modules.Ast.typ option)
                    * Modules.Ast.typ
                    * (Modules.Ast.expr -> Modules.Ast.expr -> Modules.Ast.expr)
                    , string) result =
          match op, t with
          | Concat, Some String | Concat, None
              -> Ok (Some String, (fun _ -> Some String), String,
                     fun l r -> BinaryExp (l, r, Concat))
          | Concat, Some Path
              -> Ok (Some String, (fun _ -> Some String), Path,
                     fun l r -> FuncExp (Id "path_of_string", 
                                         [BinaryExp (l, r, Concat)]))
          | Concat, _ -> Error "Incorrect type for concat (produces string)"
          | Equals, Some Bool | Equals, None
              -> Ok (None, (fun t -> Some t), Bool,
                     fun l r -> BinaryExp (l, r, Eq))
          | Equals, _ -> Error "Incorrect type for equals (produces bool)"
          | And, Some Bool | And, None
              -> Ok (Some Bool, (fun _ -> Some Bool), Bool,
                     fun l r -> BinaryExp (l, r, And))
          | And, _ -> Error "Incorrect type for and (produces bool)"
          | Or, Some Bool | Or, None
              -> Ok (Some Bool, (fun _ -> Some Bool), Bool,
                     fun l r -> BinaryExp (l, r, Or))
          | Or, _ -> Error "Incorrect type for or (produces bool)"
        in Result.bind op_info
          (fun (lhs_t, rhs_t, ret_typ, op) ->
            Result.bind (codegen_value lhs lhs_t play_env)
              (fun (lhs, lhs_t) ->
                Result.bind (codegen_value rhs (rhs_t lhs_t) play_env)
                (fun (rhs, _) -> Ok (op lhs rhs, ret_typ))))
    | Dot (ex, field) ->
        Result.bind (codegen_value ex None play_env)
        (fun (ex, ty) ->
          match ty with
          | Named nm ->
              begin match Modules.Codegen.UniqueMap.find nm tys with
              | None -> Error "Internal Error: type undefined"
              | Some typ ->
                  let rec process_for_field (typ: Modules.Codegen.typ)
                    : (Modules.Ast.expr * Modules.Ast.typ, string) result =
                    match typ with
                    | Placeholder { contents = Some typ } -> process_for_field typ
                    | Placeholder { contents = None } -> Error "Internal Error: unknown placeholder"
                    | Struct (_, fields) ->
                        begin match Modules.Codegen.StringMap.find_opt field fields with
                        | None -> Error (Printf.sprintf "Value has no field '%s'" field)
                        | Some t ->
                            (* TODO: Check type *)
                            (* TODO: Add String <-> Path coercions *)
                            Ok (Field (ex, field), codegen_type_to_ast_typ t)
                        end
                    | _ -> Error (Printf.sprintf "Value has no field '%s'" field)
                  in process_for_field typ
              end
          | _ -> Error (Printf.sprintf "Value has no field '%s'" field))
  in let process_module_use nm args =
    match args with
    | `O map ->
        let rec process_module_args map res =
          match map with
          | [] -> Result.map_error (String.concat "\n") res#to_mod
          | (field, v) :: tl ->
              match Result.map (res#add_arg field) (process_value v) with
              | Ok () -> process_module_args tl res
              | Error msg -> Error msg
        in process_module_args map (new mod_result(nm))
    | `Null -> (* No arguments *)
        Result.map_error (String.concat "\n") (new mod_result(nm))#to_mod
    | _ -> (* Free form arguments are not yet handled, treat as if there was
            * nothing there *)
        Result.map_error (String.concat "\n") (new mod_result(nm))#to_mod
  in let process_task t =
    match t with
    | `O map ->
        let rec process_task_fields map res =
          match map with
          | [] -> Result.map_error (String.concat "\n") res#to_task
          | (field, v) :: tl ->
              match
                match field with
                | "name" -> Result.map res#add_name (process_string v)
                | "register" -> Result.map res#add_register (process_string v)
                | "ignore_errors" -> Result.map res#add_ignore_errors (process_bool v)
                | "become" -> Result.map res#add_become (process_bool v)
                | "when" -> Result.map res#add_when (process_condition v)
                | "with_items" | "loop"
                  -> Result.map (fun v -> res#add_loop (ItemLoop v)) (process_value v)
                | "with_fileglob"
                  -> Result.map (fun v -> res#add_loop (FileGlob v)) (process_value v)
                | "notify"
                  -> Result.map res#add_notify (process_string_list v)
                | "tags" -> Ok () (* TODO: We just ignore tags for now *)
                | "loop_control" -> Ok () (* TODO: We just ignore loop_control *)
                | _ -> Result.map res#add_module (process_module_use field v)
              with
              | Ok () -> process_task_fields tl res
              | Error msg -> Error msg
        in process_task_fields map (new task_result)
    | _      -> Error "Expected task to be a mapping with fields"
  in let process_tasks ts =
    match ts with
    | `A seq ->
        let rec process ts =
          match ts with
          | [] -> Ok []
          | t :: ts ->
              match process_task t, process ts with
              | Ok t, Ok ts          -> Ok (t :: ts)
              | Ok _, Error msg      -> Error msg
              | Error msg, Ok _      -> Error msg
              | Error mhd, Error mtl -> Error (mhd ^ "\n" ^ mtl)
        in process seq
    | _      -> Error "expected sequence of tasks"
  in let process_handler h =
    match h with
    | `O map ->
        let rec process_handler_fields map res =
          match map with
          | [] -> Result.map_error (String.concat "\n") res#to_handler
          | (field, v) :: tl ->
              match
                match field with
                | "name" -> Result.map res#add_name (process_string v)
                | "listen" -> Result.map res#add_listen (process_string v)
                | "register" -> Result.map res#add_register (process_string v)
                | "ignore_errors" -> Result.map res#add_ignore_errors (process_bool v)
                | "become" -> Result.map res#add_become (process_bool v)
                | "when" -> Result.map res#add_when (process_condition v)
                | "with_items" | "loop"
                  -> Result.map (fun v -> res#add_loop (ItemLoop v)) (process_value v)
                | "with_fileglob"
                  -> Result.map (fun v -> res#add_loop (FileGlob v)) (process_value v)
                | _ -> Result.map res#add_module (process_module_use field v)
              with
              | Ok () -> process_handler_fields tl res
              | Error msg -> Error msg
        in process_handler_fields map (new handler_result)
    | _ -> Error "Expected handler to be a mapping with fields"
  in let process_handlers hs =
    match hs with
    | `A seq ->
        let rec process ts =
          match ts with
          | [] -> Ok []
          | h :: hs ->
              match process_handler h, process hs with
              | Ok h, Ok hs           -> Ok (h :: hs)
              | Ok _, Error msg       -> Error msg
              | Error msg, Ok _       -> Error msg
              | Error mhd, Error mtl  -> Error (mhd ^ "\n" ^ mtl)
        in process seq
    | _ -> Error "expected sequence of handlers"
  in let codegen_module_invocation m (play_env: play_env) =
    let module_name = String.split_on_char '.' m.mod_name
    in let module_expr =
      match module_name with
      | [] -> failwith "String.split_on_char always returns non-empty list"
      | base :: fields ->
          List.fold_left (fun m f -> Modules.Ast.Field (m, f)) (Id base) fields
    in
    (* Lookup the module, we need information on the types of its arguments *)
    match Modules.Codegen.find_module_def module_name env with
    | None -> Error (Printf.sprintf "Could not find module %s" m.mod_name)
    | Some mod_info ->
        let arg_aliases = mod_info.alias_map
        in let arg_types = mod_info.args
        in let res_type = mod_info.ret_type
        in let module_args =
          let rec process_args args =
            match args with
            | [] -> Ok []
            | (nm, v) :: tl ->
                let canon_name =
                  match Modules.Codegen.StringMap.find_opt nm arg_aliases with
                  | None -> nm
                  | Some c -> c
                in match Modules.Codegen.StringMap.find_opt canon_name arg_types with
                | None -> Error (Printf.sprintf "No argument %s of module %s" nm m.mod_name)
                | Some t ->
                    match codegen_value v (Some t) play_env with
                    | Ok (e, _) -> Result.map (fun tl -> (canon_name, e) :: tl) (process_args tl)
                    | Error msg -> Error msg
          in process_args m.args
        in Result.map
          (fun args -> (Modules.Ast.ModuleExp (module_expr, args), res_type))
          module_args
  in let codegen_task (t : task) (play_env: play_env)
    : (Modules.Ast.stmt list, string) result =
    let () =
      match t.loop with
      | None -> ()
      | Some (ItemLoop v) ->
          (* Item loops may end up with the item type constrained by a usage
           * to give us more information, but we'll first try to type it in
           * case the item's usage is not in a constrained context *)
          begin match codegen_value v None play_env with
          | Ok (_, List t) -> Hashtbl.add play_env "item" (Unknown ("item", t))
          | _ -> Hashtbl.add play_env "item" (Unknown ("item", String))
          end
      | Some (FileGlob _) -> Hashtbl.add play_env "item" (Concrete Path)
    in Result.bind (codegen_module_invocation t.module_invoke play_env)
      (fun (modul, typ) ->
        let body = 
          let module_invoke = Modules.Ast.LetStmt (t.register, modul)
          in let error_checking =
            if t.ignore_errors then []
            else [Modules.Ast.Assert (UnaryExp (Field (Id t.register, "failed"), Not))]
          in if t.become
          (* If become was specified, we escalate privilege to root by
           * 1) recording the current user and is_root property
           * 2) assert that the current user can escalate
           * 3) setting the user to "root" and setting is_root to true
           * 4) after executing the module reset the user and is_root
           *)
          then Modules.Ast.LetStmt ("#old_user", Field (FuncExp (Id "env", []), "active_user"))
            :: LetStmt ("#old_group", Field (FuncExp (Id "env", []), "active_group"))
            :: LetStmt ("#old_root", Field (FuncExp (Id "env", []), "is_root"))
            :: Assert (FuncExp (Id "can_escalate", [Id "#old_user"]))
            :: Assign (Field (FuncExp (Id "env", []), "active_user"), StringLit "root")
            :: Assign (Field (FuncExp (Id "env", []), "active_group"), StringLit "root")
            :: Assign (Field (FuncExp (Id "env", []), "is_root"), BoolLit true)
            :: module_invoke
            :: Assign (Field (FuncExp (Id "env", []), "active_user"), Id "#old_user")
            :: Assign (Field (FuncExp (Id "env", []), "active_group"), Id "#old_group")
            :: Assign (Field (FuncExp (Id "env", []), "is_root"), Id "#old_root")
            :: error_checking
          else module_invoke :: error_checking
        in let conditioned =
          match t.condition with
          | None -> Ok body
          | Some cond ->
              Result.bind
                (codegen_value (list_to_and cond) (Some Bool) play_env)
                (fun (c, _) -> Ok [Modules.Ast.IfThenElse (c, body, [])])
        in let () =
          if t.register <> "_" then Hashtbl.add play_env t.register (Concrete typ)
        in let looped =
          match t.loop with
          | None -> conditioned
          | Some (ItemLoop lst) ->
              let item_typ = match Hashtbl.find play_env "item" with
                             (* If there's no known type for the items, just
                                treat them as strings *)
                             | Unknown _ -> Modules.Ast.String
                             | Concrete t -> t
              in Result.bind (codegen_value lst (Some (List item_typ)) play_env)
              (fun (lst, _) ->
                Result.bind conditioned
                  (fun conditioned ->
                    Ok [Modules.Ast.ForLoop ("item", lst, conditioned)]))
          | Some (FileGlob glob) ->
              (* Per the documentation: https://docs.ansible.com/ansible/latest/collections/ansible/builtin/fileglob_lookup.html
                 with_fileglob will only return files, so within the loop we
                 add assertions that the files exist and are just files *)
              Result.bind (codegen_value glob (Some (List String)) play_env)
                (fun (glob, _) ->
                  let files = Modules.Ast.FuncExp 
                    (* We use the file_glob uninterpreted function defined in
                     * the find module *)
                    (Id "file_glob",
                      [ glob
                      ; EnumExp (Id "find_file_type", None, "file", [])
                      ; EnumExp (Id "file_system", None, "local", []) ])
                  in Result.bind conditioned
                    (fun conditioned ->
                      let item_file =
                        Modules.Ast.FuncExp (Id "fs",
                          [Id "item"; EnumExp (Id "file_system", None, "local", [])])
                      in let assert_false = Modules.Ast.Assert (BoolLit false)
                      in let loop_body =
                        Modules.Ast.AssertExists item_file
                        :: Match (Field (item_file, "fs_type"),
                          [ (("file_type", None, "file", ["_"]), [])
                          ; (("file_type", None, "directory", ["_"]), [assert_false])
                          ; (("file_type", None, "hard", ["_"]), [assert_false])
                          ; (("file_type", None, "link", ["_"]), [assert_false])
                          ])
                        :: conditioned
                      in Ok [Modules.Ast.ForLoop ("item", files, loop_body)]))
        in let () = if Option.is_some t.loop then Hashtbl.remove play_env "item"
        in looped)
  in let codegen_play (play : play) : (Modules.Ast.stmt list, string) result =
    (* TODO: make use of hosts field? *)
    (* TODO: We are currently ignoring handlers *)
    let rec codegen_tasks ts play_env =
      match ts with
      | [] -> Ok []
      | t :: tl ->
          match codegen_task t play_env with
          | Ok t -> Result.map (fun tl -> t @ tl) (codegen_tasks tl play_env)
          | Error msg -> Error msg
    in let play_env = Hashtbl.create 10
    in let tasks = codegen_tasks play.tasks play_env
    in let with_become =
      (* Handle become as above *)
      Result.map
      (fun tasks ->
        if play.become
        then Modules.Ast.Assert (FuncExp (Id "can_escalate",
                                [Field (FuncExp (Id "env", []), "active_user")]))
          :: Assign (Field (FuncExp (Id "env", []), "active_user"), StringLit "root")
          :: Assign (Field (FuncExp (Id "env", []), "active_group"), StringLit "root")
          :: Assign (Field (FuncExp (Id "env", []), "is_root"), BoolLit true)
          :: tasks
        else tasks)
      tasks
    (* Set the user by env().active_user = remote_user
     * and set is_root based on what we know of it *)
    in Result.map
      (fun play_body ->
        Modules.Ast.Assign
          (Field (FuncExp (Id "env", []), "active_user"),
           StringLit play.remote_user)
        :: match play.is_root with
           | None -> play_body
           | Some is_root ->
              Modules.Ast.Assign
                (Field (FuncExp (Id "env", []), "is_root"), BoolLit is_root)
              :: play_body)
      with_become
  in let process_play play =
    match play with
    | `O map ->
        let rec process_play_fields map res =
          match map with
          | [] -> Result.map_error (String.concat "\n") res#to_play
          | (field, v) :: tl ->
              match
                match field with
                | "name"        -> Result.map res#add_name (process_string v)
                | "hosts"       -> Result.map res#add_hosts (process_string v)
                | "remote_user" -> Result.map res#add_remote_user (process_string v)
                | "tasks"       -> Result.map res#add_tasks (process_tasks v)
                | "become"      -> Result.map res#add_become (process_bool v)
                | "handlers"    -> Result.map res#add_handlers (process_handlers v)
                | _             -> Error (Printf.sprintf "unrecognized field '%s' in play" field)
              with
              | Ok ()     -> process_play_fields tl res
              | Error msg -> Error msg
        in Result.bind (process_play_fields map (new play_result)) codegen_play
    | _ -> Error ("Expected play to be a mapping with fields")
  in let rec process_plays plays =
    match plays with
    | [] -> Ok []
    | hd :: tl ->
        match process_play hd, process_plays tl with
        | Ok hd, Ok tl -> Ok (hd @ tl)
        | Ok _, Error msg -> Error msg
        | Error msg, Ok _ -> Error msg
        | Error mhd, Error mtl -> Error (mhd ^ "\n" ^ mtl)
  in let process_yaml code =
    match code with
    | `A seq -> process_plays seq
    | _ -> Error ("Expected top-level of an ansible playbook to be a sequence of plays")
  in let ch = open_in file
  in let s = really_input_string ch (in_channel_length ch)
  in let () = close_in ch
  in match Yaml.of_string s with
  | Error (`Msg msg) -> Error msg
  | Ok contents -> Result.map
      (fun body ->
        (* We add the following preamble to setup the environment the way we
         * want it:
         * - assert exists env();
         * - assert env().time_counter = 0;
         * - assert env().last_reboot = -1; *)
        Modules.Ast.AssertExists (FuncExp (Id "env", []))
        :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"), IntLit 0, Eq))
        :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "last_reboot"), IntLit (-1), Eq))
        :: body)
      (process_yaml contents)
