(* Note: even though the YAML spec requires that maps have unique labels, the
 * OCaml YAML library does not seem to enforce this, so our handling of
 * playbooks and tasks handles and reports errors if a field is set multiple
 * times *)
let ( let^ ) r f = Result.bind r f

module Jinterp = Jingoo.Jg_interp
module Jtypes = Jingoo.Jg_types

module Ops = Ast
module Ast = Ast.Parsed

(* Utilities for constructing the AST *)
class mod_result name =
  object
    val args           = (Hashtbl.create 10 : (string, Ast.value) Hashtbl.t)

    val mutable errors = ([] : string list)

    method add_arg nm v =
      if Hashtbl.mem args nm
      then errors <- Printf.sprintf "Argument %s appears multiple times" nm
                  :: errors
      else
        Hashtbl.add args nm v

    method to_mod : (Ast.mod_use, string list) result =
      if not (List.is_empty errors)
      then Error errors
      else Ok { mod_name = name; args = List.of_seq (Hashtbl.to_seq args) }
  end

type task_body =
  | Module of Ast.mod_use
  | Block  of {
      tasks: Ast.task list option;
      rescue: Ast.task list option;
      always: Ast.task list option
    }

let coerce_task_body (t : task_body option) : (Ast.task_body, string list) result =
  match t with
  | None -> Error ["no task body"]
  | Some (Module m) -> Ok (Module m)
  | Some (Block { tasks = None; _ }) -> Error ["no task body"]
  | Some (Block { tasks = Some tasks; rescue; always }) ->
      Ok (Block { tasks = tasks; rescue = rescue; always = always })

class task_result =
  object
    val mutable name          = (None : string option)
    val mutable register      = (None : string option)
    val mutable ignore_errors = (None : bool option)
    val mutable condition     = (None : Ast.value option)
    val mutable loop          = (None : Ast.loop_kind option)
    val mutable body          = (None : task_body option)

    val mutable notify        = (None : Ast.value list option)
    val mutable become        = (None : bool option)
    val mutable become_user   = (None : string option)

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
      match body with
      | None -> body <- Some (Module m)
      | Some (Module c) -> errors <-
        Printf.sprintf "Multiple modules specified: %s and %s" c.mod_name m.mod_name
        :: errors
      | Some (Block _) -> errors <-
        Printf.sprintf "Task contains both block and module %s" m.mod_name
        :: errors

    method add_block ts =
      match body with
      | None ->
          body <- Some (Block { tasks = Some ts; rescue = None; always = None })
      | Some (Module c) -> errors <-
        Printf.sprintf "Task contains both block and module %s" c.mod_name
        :: errors
      | Some (Block b) ->
          match b.tasks with
          | None ->
              body <- Some (Block { tasks = Some ts; rescue = b.rescue; always = b.always })
          | Some _ ->
              errors <- "Task contains multiple block sections" :: errors
    method add_rescue ts =
      match body with
      | None -> 
          body <- Some (Block { tasks = None; rescue = Some ts; always = None })
      | Some (Module c) -> errors <-
          Printf.sprintf "Task contains rescue and module %s" c.mod_name
          :: errors
      | Some (Block b) ->
          match b.rescue with
          | None ->
              body <- Some (Block { tasks = b.tasks; rescue = Some ts; always = b.always })
          | Some _ ->
              errors <- "Task contains multiple rescue sections" :: errors
    method add_always ts =
      match body with
      | None -> 
          body <- Some (Block { tasks = None; rescue = None; always = Some ts })
      | Some (Module c) -> errors <-
          Printf.sprintf "Task contains always and module %s" c.mod_name
          :: errors
      | Some (Block b) ->
          match b.always with
          | None ->
              body <- Some (Block { tasks = b.tasks; rescue = b.rescue; always = Some ts })
          | Some _ ->
              errors <- "Task contains multiple always sections" :: errors

    method add_notify hs =
      match notify with
      | None -> notify <- Some hs
      | _    -> errors <- "Multiple notify fields" :: errors

    method add_become b =
      match become with
      | None -> become <- Some b
      | _    -> errors <- "Multiple become fields" :: errors
    method add_become_user n =
      match become_user with
      | None -> become_user <- Some n
      | _    -> errors <- "Multiple become_user fields" :: errors

    method to_task : (Ast.task, string list) result =
      if not (List.is_empty errors)
      then Error errors
      else
        let^ body = coerce_task_body body
        in Ok { Ast.name      = Option.value name ~default:""
              ; register      = Option.value register ~default:"_"
              ; ignore_errors = Option.value ignore_errors ~default:false
              ; condition     = condition
              ; loop          = loop
              ; body          = body
              ; notify        = Option.value notify ~default:[]
              ; become        = Option.value become ~default:false
              ; become_user   = Option.value become_user ~default:"root"}
  end

class handler_result =
  object
    val mutable name          = (None : string option)
    val mutable listen        = (None : string option)
    val mutable register      = (None : string option)
    val mutable module_invoke = (None : Ast.mod_use option)

    val mutable ignore_errors = (None : bool option)
    val mutable condition     = (None : Ast.value option)
    val mutable loop          = (None : Ast.loop_kind option)
    val mutable become        = (None : bool option)
    val mutable become_user   = (None : string option)

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
      | _    -> errors <- "Multiple become_user fields" :: errors
    method add_become_user n =
      match become_user with
      | None -> become_user <- Some n
      | _    -> errors <- "Multiple become_user fields" :: errors

    method to_handler : (Ast.handler, string list) result =
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
                   ; become        = Option.value become ~default:false
                   ; become_user   = Option.value become_user ~default:"root" }
  end

class play_result =
  object
    val mutable name        = (None : string option)
    val mutable hosts       = (None : string option)
    val mutable remote_user = (None : string option)
    val mutable pre_tasks   = (None : Ast.task list option)
    val mutable tasks       = (None : Ast.task list option)
    val mutable post_tasks  = (None : Ast.task list option)
    val mutable handlers    = (None : Ast.handler list option)

    val mutable become      = (None : bool option)
    val mutable become_user = (None : string option)

    val mutable vars        = (None : (string * Ast.value) list option)

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

    method add_pre_tasks ts =
      match pre_tasks with
      | None -> pre_tasks <- Some ts
      | _    -> errors <- "Multiple pre_tasks fields" :: errors
    method add_tasks ts =
      match tasks with
      | None -> tasks <- Some ts
      | _    -> errors <- "Multiple tasks fields" :: errors
    method add_post_tasks ts =
      match post_tasks with
      | None -> post_tasks <- Some ts
      | _    -> errors <- "Multiple post_tasks fields" :: errors
    method add_handlers hs =
      match handlers with
      | None -> handlers <- Some hs
      | _    -> errors <- "Multiple handlers fields" :: errors

    method add_become b =
      match become with
      | None -> become <- Some b
      | _    -> errors <- "Multiple become fields" :: errors
    method add_become_user n =
      match become_user with
      | None -> become_user <- Some n
      | _    -> errors <- "Multiple become_user fields" :: errors

    method add_vars vs =
      match vars with
      | None -> vars <- Some vs
      | _    -> errors <- "Multiple vars fields" :: errors

    method to_play : (Ast.play, string list) result =
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
               ; become_user  = Option.value become_user ~default:"root"
               ; pre_tasks    = pre_tasks
               ; tasks        = t
               ; post_tasks   = post_tasks
               ; handlers     = Option.value handlers ~default:[]
               ; vars         = Option.value vars ~default:[] }
  end

(* Utilities *)
let iter_res (l : 'a list) (f : 'a -> (unit, 'e) result) : (unit, 'e) result =
  let rec iter (xs : 'a list) =
    match xs with
    | [] -> Ok ()
    | x :: xs -> let^ () = f x in iter xs
  in iter l

(* Code for processing the Ansible YAML into the AST form *)

(* Convert Jinja expression into AST *)
let rec jinja_to_value (j : Jtypes.ast) : (Ast.value, string) result =
  let rec jlit_to_value (j : Jtypes.tvalue) : (Ast.value, string) result =
    match j with
    | Tnull -> Ok (String "")
    | Tint i -> Ok (Int i)
    | Tbool b -> Ok (Bool b)
    | Tfloat f -> Ok (Float f)
    | Tstr s -> Ok (String s)
    | Tlist xs ->
        let^ xs =
          let rec convert (xs : Jtypes.tvalue list) =
            match xs with
            | [] -> Ok []
            | x :: xs ->
                let^ x = jlit_to_value x
                in let^ xs = convert xs
                in Ok (x :: xs)
          in convert xs
        in Ok (Ast.List xs)
    | _ -> Error "Unsupported Jinja literal value"
  in let rec jexpr_to_value (j : Jtypes.expression)
    : (Ast.value, string) result =
    match j with
    | IdentExpr nm ->
        Ok (Ident nm)
    | LiteralExpr v ->
        jlit_to_value v
    | NotOpExpr e
    | NegativeOpExpr e ->
        let op : Ops.unary =
          match j with
          | NotOpExpr _ -> Not
          | NegativeOpExpr _ -> Neg
          | _ -> failwith "Matching error"
        in let^ e = jexpr_to_value e
        in Ok (Ast.Unary (e, op))
    | PlusOpExpr (lhs, rhs)
    | MinusOpExpr (lhs, rhs)
    | TimesOpExpr (lhs, rhs)
    | PowerOpExpr (lhs, rhs)
    | DivOpExpr (lhs, rhs)
    | ModOpExpr (lhs, rhs)
    | AndOpExpr (lhs, rhs)
    | OrOpExpr (lhs, rhs)
    | NotEqOpExpr (lhs, rhs)
    | EqEqOpExpr (lhs, rhs)
    | LtOpExpr (lhs, rhs)
    | GtOpExpr (lhs, rhs)
    | LtEqOpExpr (lhs, rhs)
    | GtEqOpExpr (lhs, rhs) ->
        let op : Ops.binary =
          match j with
          | PlusOpExpr (_, _) -> Add
          | MinusOpExpr (_, _) -> Sub
          | TimesOpExpr (_, _) -> Mul
          | PowerOpExpr (_, _) -> Pow
          | DivOpExpr (_, _) -> Div
          | ModOpExpr (_, _) -> Mod
          | AndOpExpr (_, _) -> And
          | OrOpExpr (_, _) -> Or
          | NotEqOpExpr (_, _) -> Neq
          | EqEqOpExpr (_, _) -> Eq
          | LtOpExpr (_, _) -> Lt
          | GtOpExpr (_, _) -> Gt
          | LtEqOpExpr (_, _) -> Le
          | GtEqOpExpr (_, _) -> Ge
          | _ -> failwith "Matching error"
        in let^ lhs = jexpr_to_value lhs
        in let^ rhs = jexpr_to_value rhs
        in Ok (Ast.Binary (lhs, op, rhs))
    | DotExpr (IdentExpr "ansible_facts", nm)
    | BracketExpr (IdentExpr "ansible_facts", LiteralExpr (Tstr nm)) ->
        Ok (Ast.Fact nm)
    | DotExpr (ex, field) ->
        let^ ex = jexpr_to_value ex
        in Ok (Ast.Dot (ex, field))
    | ApplyExpr (IdentExpr "lower", [(None, arg)]) ->
        let^ arg = jexpr_to_value arg
        in Ok (Ast.Unary (arg, Lower))
    | TestOpExpr (ex, IdentExpr "success") ->
        let^ ex = jexpr_to_value ex
        in Ok (Ast.Dot (ex, "success"))
    | TestOpExpr (IdentExpr var, IdentExpr "defined") ->
        Ok (Ast.VarDefined var)
    | InOpExpr (lhs, ListExpr lst) ->
        let^ lhs = jexpr_to_value lhs
        in List.fold_left (fun res rhs ->
          let^ res = res
          in let^ rhs = jexpr_to_value rhs
          in Ok (Ast.Binary (res, Or, Binary (lhs, Eq, rhs))))
          (Ok (Bool false))
          lst
    | TernaryOpExpr (cond, thn, els) ->
        let^ cond = jexpr_to_value cond
        in let^ thn = jexpr_to_value thn
        in let^ els = jexpr_to_value els
        in Ok (Ast.Ternary (cond, thn, els))
    | _ -> Error "Unhandled Jinja expression form"

  in let jstmt_to_value (j : Jtypes.statement) : (Ast.value, string) result =
    match j with
    | TextStatement s   -> Ok (String s)
    | ExpandStatement e -> jexpr_to_value e
    | _ -> Error "Unsupported Jinja form"
  in match j with
  | [] -> Ok (String "")
  | [e] -> jstmt_to_value e
  | e :: js ->
      let^ e = jstmt_to_value e
      in let^ js = jinja_to_value js
      in Ok (Ast.Binary (e, Concat, js))

(* Coerce values into a string, if possible *)
let process_string (y : Yaml.value) : (string, string) result =
  match y with
  | `String s -> Ok s
  | `Bool   b -> Ok (string_of_bool b)
  | `Float  f -> Ok (string_of_float f)
  | `Null     -> Ok "" (* Sometimes null is used as an empty string *)
  | `A _      -> Error "Expected string, found sequence"
  | `O _      -> Error "Expected string, found mapping"

(* Coerce value into a list of strings *)
let process_string_list (y : Yaml.value) : (string list, string) result =
  match y with
  | `String s -> Ok [s]
  | `Bool b   -> Ok [string_of_bool b]
  | `Float f  -> Ok [string_of_float f]
  | `Null     -> Ok []
  | `A vs     ->
      let rec process (vs : Yaml.value list) : (string list, string) result =
        match vs with
        | [] -> Ok []
        | hd :: tl ->
            let^ hd = process_string hd
            in let^ tl = process tl
            in Ok (hd :: tl)
      in process vs
  | `O _ -> Error "Expected string list, found mapping"

let process_bool (y : Yaml.value) : (bool, string) result =
  match y with
  | `Bool b -> Ok b
  | _ -> Error "expected a bool"

let rec process_value (y : Yaml.value) : (Ast.value, string) result =
  match y with
  | `Null -> Ok (String "")
  | `Bool b -> Ok (Bool b)
  | `Float f -> Ok (Float f)
  | `String s ->
      begin try jinja_to_value (Jinterp.ast_from_string s)
      with _ -> Error "jinja parsing error" end
  | `A vs ->
      let rec process (vs : Yaml.value list) : (Ast.value list, string) result =
        match vs with
        | [] -> Ok []
        | hd :: tl ->
            let^ hd = process_value hd
            in let^ tl = process tl
            in Ok (hd :: tl)
      in let^ vs = process vs
      in Ok (Ast.List vs)
  | `O fields ->
      let rec process (vs : (string * Yaml.value) list)
        : ((string * Ast.value) list, string) result =
        match vs with
        | [] -> Ok []
        | (f, hd) :: tl ->
            let^ hd = process_value hd
            in let^ tl = process tl
            in Ok ((f, hd) :: tl)
      in let^ fields = process fields
      in Ok (Ast.Record fields)

let process_value_list (y : Yaml.value) : (Ast.value list, string) result =
  let^ v = process_value y
  in match v with
  | Ast.List vs -> Ok vs
  | _ -> Ok [v]

let rec process_condition (y : Yaml.value) : (Ast.value, string) result =
  match y with
  | `Null    -> Ok (Bool true) (* Empty list is treated as true *)
  | `Bool b  -> Ok (Bool b)
  | `Float f -> Ok (Float f)
  | `String s ->
      begin try 
        jinja_to_value (Jinterp.ast_from_string (Printf.sprintf "{{ %s }}" s))
      with _ -> Error "jinja parsing error" end
  | `A vs ->
      let rec process_elems (vs : Yaml.value list)
        : (Ast.value, string) result =
        match vs with
        | [] -> Ok (Bool true)
        | hd :: tl ->
            let^ hd = process_condition hd
            in let^ tl = process_elems tl
            in Ok (Ast.Binary (hd, And, tl))
      in process_elems vs
  | `O _ -> Error "Expected condition, found mapping"

let process_vars (y : Yaml.value)
  : ((string * Ast.value) list, string) result =
  match y with
  | `O map ->
      let rec process (vs : (string * Yaml.value) list) =
        match vs with
        | [] -> Ok []
        | (nm, hd) :: tl ->
            let^ hd = process_value hd
            in let^ tl = process tl
            in Ok ((nm, hd) :: tl)
      in process map
  | `Null -> Ok []
  | _ -> Error "Expected variables as field mapping"

let process_module_use (nm : string) (args : Yaml.value)
  : (Ast.mod_use, string) result =
  let res = new mod_result(nm)
  in let^ () =
    match args with
    | `O map ->
        iter_res map (fun (field, v) ->
          let^ v = process_value v
          in Ok (res#add_arg field v))
    | `Null -> Ok () (* No arguments *)
    | _ -> Error "Free-form arguments not supported"
  in Result.map_error (String.concat "\n") res#to_mod

let rec process_task (y : Yaml.value) : (Ast.task, string) result =
  match y with
  | `O map ->
      let task = new task_result
      in let^ () = iter_res map (fun (field, v) ->
        match field with
        | "name" ->
            Result.map task#add_name (process_string v)
        | "register" ->
            Result.map task#add_register (process_string v)
        | "ignore_errors" ->
            Result.map task#add_ignore_errors (process_bool v)
        | "become" ->
            Result.map task#add_become (process_bool v)
        | "become_user" ->
            Result.map task#add_become_user (process_string v)
        | "become_method" ->
            Ok () (* TODO *)
        | "when" ->
            Result.map task#add_when (process_condition v)
        | "with_items" | "loop" ->
            Result.map (fun v -> task#add_loop (ItemLoop v)) (process_value v)
        | "with_fileglob" ->
            Result.map (fun v -> task#add_loop (FileGlob v)) (process_value v)
        | "notify" ->
            Result.map task#add_notify (process_value_list v)
        | "tags" ->
            Ok () (* TODO *)
        | "loop_control" ->
            Ok () (* TODO *)
        | "no_log" ->
            Ok () (* TODO *)
        | "changed_when" ->
            Ok () (* TODO *)
        | "block" ->
            Result.map task#add_block (process_tasks v)
        | _ ->
            Result.map task#add_module (process_module_use field v))
      in Result.map_error (String.concat "\n") task#to_task
  | _ -> Error "Expected task to be a mapping with fields"

and process_tasks (y : Yaml.value) : (Ast.task list, string) result =
  let rec process_list (ts : Yaml.value list) =
    match ts with
    | [] -> Ok []
    | hd :: tl ->
        let^ hd = process_task hd
        in let^ tl = process_list tl
        in Ok (hd :: tl)
  in match y with
  | `A seq -> process_list seq
  | _ -> Error "Expected sequence of tasks"

let process_handler (y : Yaml.value) : (Ast.handler, string) result =
  match y with
  | `O map ->
      let handler = new handler_result
      in let^ () = iter_res map (fun (field, v) ->
        match field with
        | "name" ->
            Result.map handler#add_name (process_string v)
        | "listen" ->
            Result.map handler#add_listen (process_string v)
        | "register" ->
            Result.map handler#add_register (process_string v)
        | "ignore_errors" ->
            Result.map handler#add_ignore_errors (process_bool v)
        | "become" ->
            Result.map handler#add_become (process_bool v)
        | "become_user" ->
            Result.map handler#add_become_user (process_string v)
        | "become_method" ->
            Ok () (* TODO *)
        | "when" ->
            Result.map handler#add_when (process_condition v)
        | "with_items" | "loop" ->
            Result.map (fun v -> handler#add_loop (ItemLoop v)) (process_value v)
        | "with_fileglob" ->
            Result.map (fun v -> handler#add_loop (FileGlob v)) (process_value v)
        | _ -> Result.map handler#add_module (process_module_use field v))
      in Result.map_error (String.concat "\n") handler#to_handler
  | _-> Error "Expected handler to be a mapping with fields"

let process_handlers (y : Yaml.value) : (Ast.handler list, string) result =
  match y with
  | `A seq ->
      let rec process_handlers (hs : Yaml.value list) =
        match hs with
        | [] -> Ok []
        | hd :: tl ->
            let^ hd = process_handler hd
            in let^ tl = process_handlers tl
            in Ok (hd :: tl)
      in process_handlers seq
  | _ -> Error "Expeected sequence of handlers"

let process_play (y : Yaml.value) : (Ast.play, string) result =
  match y with
  | `O map ->
      let play = new play_result
      in let^ () = iter_res map (fun (field, v) ->
          match field with
          | "name" ->
              Result.map play#add_name (process_string v)
          | "hosts" ->
              Result.map play#add_hosts (process_string v)
          | "remote_user" ->
              Result.map play#add_remote_user (process_string v)
          | "pre_tasks" ->
              Result.map play#add_pre_tasks (process_tasks v)
          | "tasks" ->
              Result.map play#add_tasks (process_tasks v)
          | "post_tasks" ->
              Result.map play#add_post_tasks (process_tasks v)
          | "become" ->
              Result.map play#add_become (process_bool v)
          | "become_user" ->
              Result.map play#add_become_user (process_string v)
          | "become_method" ->
              Ok () (* TODO *)
          | "handlers" ->
              Result.map play#add_handlers (process_handlers v)
          | "vars" ->
              Result.map play#add_vars (process_vars v)
          | _ ->
              Error (Printf.sprintf "unrecognized field '%s' for play" field))
      in Result.map_error (String.concat "\n") play#to_play
  | _ -> Error "Expected play to be a mapping with fields"

let process_playbook (y : Yaml.value) : (Ast.playbook, string) result =
  let rec process_plays (y : Yaml.value list) : (Ast.playbook, string) result =
    match y with
    | [] -> Ok []
    | hd :: tl ->
        let^ hd = process_play hd
        in let^ tl = process_plays tl
        in Ok (hd :: tl)
  in match y with
  | `A seq -> process_plays seq
  | _ -> Error "Ansible playbook must be a list of plays"

let parse_ansible (filename : string) : (Ast.playbook, string) result =
  let ch = open_in filename
  in let s = really_input_string ch (in_channel_length ch)
  in let () = close_in ch
  in match Yaml.of_string s with
  | Error (`Msg msg) -> Error msg
  | Ok contents -> process_playbook contents
