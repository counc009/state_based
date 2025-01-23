(* Note: even though the YAML spec requires that maps have unique labels, the
 * OCaml YAML library does not seem to enforce this, so our handling of
 * playbooks and tasks handles and reports errors if a field is set multiple
 * times *)

type value =
  | String of string
  | Float  of float
  | Bool   of bool
  | List   of value list

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

type task = {
  name: string;
  register: string;
  ignore_errors: bool;
  module_invoke: mod_use
}

class task_result =
  object
    val mutable name          = (None : string option)
    val mutable register      = (None : string option)
    val mutable ignore_errors = (None : bool option)
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
    | `String s -> Ok (String s)
    | `A vs     ->
        let rec process vs =
          match vs with
          | [] -> Ok []
          | hd :: tl ->
              match process_value hd with
              | Ok h -> Result.map (fun tl -> h :: tl) (process tl)
              | Error msg -> Error msg
        in Result.map (fun vs -> List vs) (process vs)
    | `O _      -> Error "expected value found mapping"
  in let rec codegen_value v (t : Modules.Ast.typ) =
    match v with
    | Float f ->
        begin match t with
        | Int ->
            if Float.is_integer f
            then Ok (Modules.Ast.IntLit (Float.to_int f))
            else Error (Printf.sprintf "Expected integer found float '%f'" f)
        | Float -> Ok (Modules.Ast.FloatLit f)
        | _ -> Error ("Incorrect type, found number")
        end
    | Bool b ->
        begin match t with
        | Bool -> Ok (Modules.Ast.BoolLit b)
        | _ -> Error ("Incorrect type, found bool")
        end
    | List vs ->
        begin match t with
        | List el ->
            (* We construct a list as a series of cons *)
            let vals =
              let rec process_vals vs =
                match vs with
                | [] -> Ok []
                | v :: vs ->
                    match codegen_value v el with
                    | Ok v ->
                        Result.map (fun tl -> v :: tl) (process_vals vs)
                    | Error msg -> Error msg
              in process_vals vs
            in Result.map
                (fun vals ->
                  List.fold_right
                    (fun v e -> 
                      Modules.Ast.EnumExp (
                        Id "list",
                        Some el,
                        "cons",
                        [v; e]))
                    vals
                    (* Nil list *)
                    (Modules.Ast.EnumExp (Id "list", Some el, "nil", [])))
                vals
        | _ -> Error ("Incorrect type, found list")
        end
    | String s ->
        (* Strings in YAML can actually represent many things in our type-system,
         * specifically strings, paths, and enum values *)
        begin match t with
        | String -> Ok (StringLit s)
        | Path   -> Ok (PathLit s)
        | Named nm ->
            begin match Modules.Codegen.UniqueMap.find nm tys with
            | None -> Error ("Internal Error: type of module argument undefined")
            | Some t ->
                let rec process_for_type (t : Modules.Codegen.typ)
                  : (Modules.Ast.expr, string) result =
                  match t with
                  | String -> Ok (StringLit s)
                  | Path   -> Ok (PathLit s)
                  | Placeholder { contents = Some t } -> process_for_type t
                  | Placeholder { contents = None } -> Error ("Internal Error: unknown placeholder")
                  | Enum constructors ->
                      begin match Modules.Codegen.StringMap.find_opt s constructors with
                      | None -> Error (Printf.sprintf
                          "Invalid value '%s' expected one of [%s]"
                          s
                          (String.concat ", " 
                            (List.map fst 
                              (Modules.Codegen.StringMap.bindings constructors))))
                      | Some (_, []) -> Ok(EnumExp (Id nm, None, s, []))
                      | Some (_, _) -> Error (Printf.sprintf
                          "Constructor %s cannot be used from Ansible, has argument"
                          s)
                      end
                  | _ -> Error ("Incorrect type, found string-like")
                in process_for_type t
            end
        | _ -> Error ("Incorrect type, found string-like")
        end
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
  in let codegen_module_invocation m =
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
                    match codegen_value v t with
                    | Ok e -> Result.map (fun tl -> (canon_name, e) :: tl) (process_args tl)
                    | Error msg -> Error msg
          in process_args m.args
        in Result.map (fun args -> Modules.Ast.ModuleExp (module_expr, args))
            module_args
  in let codegen_task (t : task) : (Modules.Ast.stmt, string) result =
    (* TODO: currently ignoring the ignore_errors flag, should insert error
     * handling here eventually *)
    Result.map
      (fun v -> Modules.Ast.LetStmt (t.register, v))
      (codegen_module_invocation t.module_invoke)
  in let codegen_play (play : play) : (Modules.Ast.stmt list, string) result =
    (* TODO: for now we're ignoring hosts and remote_user...
     * remote_user should probably be used to update user listed in env() *)
    let rec codegen_tasks ts =
      match ts with
      | [] -> Ok []
      | t :: tl ->
          match codegen_task t with
          | Ok t -> Result.map (fun tl -> t :: tl) (codegen_tasks tl)
          | Error msg -> Error msg
    in let tasks = codegen_tasks play.tasks
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
                | _             -> Error "unrecognized field in play"
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
