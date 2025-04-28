(* Note: even though the YAML spec requires that maps have unique labels, the
 * OCaml YAML library does not seem to enforce this, so our handling of
 * playbooks and tasks handles and reports errors if a field is set multiple
 * times *)

module Jinterp = Jingoo.Jg_interp
module Jtypes = Jingoo.Jg_types

type unary  = Not
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
  module_invoke: mod_use
}

class task_result =
  object
    val mutable name          = (None : string option)
    val mutable register      = (None : string option)
    val mutable ignore_errors = (None : bool option)
    val mutable condition     = (None : value option)
    val mutable loop          = (None : loop_kind option)
    val mutable module_invoke = (None : mod_use option)

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
               ; module_invoke = m }
  end

type play = {
  name        : string;
  hosts       : string option;
  remote_user : string;
  tasks       : task list
}

class play_result =
  object
    val mutable name        = (None : string option)
    val mutable hosts       = (None : string option)
    val mutable remote_user = (None : string option)
    val mutable tasks       = (None : task list option)

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
               ; tasks        = t }
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

type var_typ = Unknown of string (* name of the variable *)
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
        | _ -> Error ("Incorrect type, found number")
        end
    | Bool b ->
        begin match t with
        | None -> Ok (Modules.Ast.BoolLit b, Modules.Ast.Bool)
        | Some Bool -> Ok (Modules.Ast.BoolLit b, Modules.Ast.Bool)
        | Some String -> Ok (Modules.Ast.StringLit (string_of_bool b), Modules.Ast.String)
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
        | _ -> Error ("Incorrect type, found string-like")
        end
    | Ident nm ->
        begin match Hashtbl.find_opt play_env nm, t with
        | Some (Concrete ty), Some t when t = ty -> Ok (Modules.Ast.Id nm, t)
        | Some (Concrete _), Some _ -> Error "mismatched types"
        | Some (Concrete ty), None -> Ok (Modules.Ast.Id nm, ty)
        | Some (Unknown _), Some t ->
            let () = Hashtbl.add play_env nm (Concrete t)
            in Ok (Modules.Ast.Id nm, t)
        | Some (Unknown _), None -> Error ("Variable of unknown type used in unknown type setting, cannot solve")
        | None, _ ->
            (* TODO: Builtin variables *)
            Error ("Unknown variable " ^ nm)
        end
    | Unary (v, op) ->
        begin match op, t with
        | Not, Some Bool | Not, None -> 
            Result.bind (codegen_value v (Some Bool) play_env)
              (fun (v, t) -> Ok (Modules.Ast.UnaryExp (v, Not), t))
        | Not, _ -> Error "Incorrect type for not (productes boolean)"
        end
    | Binary (lhs, op, rhs) ->
        let op_info : (Modules.Ast.typ option 
                    * (Modules.Ast.typ -> Modules.Ast.typ option)
                    * Modules.Ast.typ
                    * Modules.Ast.binary, string) result =
          match op, t with
          | Concat, Some String | Concat, None
              -> Ok (Some String, (fun _ -> Some String), String, Concat)
          | Concat, _ -> Error "Incorrect type for concat (produces string)"
          | Equals, Some Bool | Equals, None
              -> Ok (None, (fun t -> Some t), Bool, Eq)
          | Equals, _ -> Error "Incorrect type for equals (produces bool)"
          | And, Some Bool | And, None -> Ok (Some Bool, (fun _ -> Some Bool), Bool, And)
          | And, _ -> Error "Incorrect type for and (produces bool)"
          | Or, Some Bool | Or, None -> Ok (Some Bool, (fun _ -> Some Bool), Bool, Or)
          | Or, _ -> Error "Incorrect type for or (produces bool)"
        in Result.bind op_info
          (fun (lhs_t, rhs_t, ret_typ, op) ->
            Result.bind (codegen_value lhs lhs_t play_env)
              (fun (lhs, lhs_t) ->
                Result.bind (codegen_value rhs (rhs_t lhs_t) play_env)
                (fun (rhs, _) -> Ok (Modules.Ast.BinaryExp (lhs, rhs, op), ret_typ))))
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
                        | Some t -> Ok (Field (ex, field), codegen_type_to_ast_typ t)
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
    | _ -> Error "Expected module argument to be a mapping with fields"
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
                | "when" -> Result.map res#add_when (process_condition v)
                | "with_items" | "loop"
                  -> Result.map (fun v -> res#add_loop (ItemLoop v)) (process_value v)
                | "with_fileglob"
                  -> Result.map (fun v -> res#add_loop (FileGlob v)) (process_value v)
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
    let () = if Option.is_some t.loop then Hashtbl.add play_env "item" (Unknown "item")
    in Result.bind (codegen_module_invocation t.module_invoke play_env)
      (fun (modul, typ) ->
        let body = Modules.Ast.LetStmt (t.register, modul)
                :: if t.ignore_errors then []
                   else [Assert (UnaryExp (Field (Id t.register, "failed"), Not))]
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
              Result.bind (codegen_value glob (Some String) play_env)
                (fun (glob, _) ->
                  let files = Modules.Ast.FuncExp (Id "file_glob", [glob])
                  in Result.bind conditioned
                    (fun conditioned ->
                      Ok [Modules.Ast.ForLoop ("item", files, conditioned)]))
        in let () = if Option.is_some t.loop then Hashtbl.remove play_env "item"
        in looped)
  in let codegen_play (play : play) : (Modules.Ast.stmt list, string) result =
    (* TODO: for now we're ignoring hosts. We should also handle setting is_root *)
    let rec codegen_tasks ts play_env =
      match ts with
      | [] -> Ok []
      | t :: tl ->
          match codegen_task t play_env with
          | Ok t -> Result.map (fun tl -> t @ tl) (codegen_tasks tl play_env)
          | Error msg -> Error msg
    in let play_env = Hashtbl.create 10
    in let tasks = codegen_tasks play.tasks play_env
    (* Set the user by env().user = remote_user *)
    in Result.map
      (fun tasks ->
        Modules.Ast.Assign 
          (Field (FuncExp (Id "env", []), "user"), 
           StringLit play.remote_user)
        :: tasks) 
      tasks
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
  | Ok contents ->
      process_yaml contents
