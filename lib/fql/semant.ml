(* We'll use a semantic analysis phase to ensure that appropriate arguments and
 * categories are selected and we'll produce a new query AST incorporating the
 * info for easy code generation.
 *
 * The goal of this analysis is to normalize the query into a form in which
 * a signle action will always be translated (mostly) the same way to the
 * module language perhaps with some pieces filled by the knowledge base.
 *)
module Target = Modules.Target.Ast_Target

open Knowledge
open Utils

module Semant(Knowledge: Knowledge_Base) = struct
  let analyze_path (p: ParseTree.vals) : (Ast.path, string) result =
    match p with
    | [s] | [Str "remote"; s] -> Ok (Remote s)
    | [Str "controller"; s] -> Ok (Controller s)
    | _ -> Error (Printf.sprintf "unhandled path specifier '%s'"
                      (ParseTree.unparse_vals p))

  let extract_bool (vs: ParseTree.vals) : (bool, string) result =
    match vs with
    | [Str "yes"] | [Str "true"] -> Ok true
    | [Str "no"] | [Str "false"] -> Ok false
    | _ -> Error (Printf.sprintf "Unknown truth value: %s"
                                 (ParseTree.unparse_vals vs))

  type file_info = { owner: ParseTree.value option;
                     group: ParseTree.value option;
                     perms: Ast.file_perms }

  let extract_file_perm (vs: ParseTree.vals) : (Ast.perm, string) result =
    let perms : Ast.perm = { owner = false; group = false; other = false }
    in let rec process (vs: ParseTree.vals) =
      match vs with
      | [] -> Ok perms
      | Str "owner" :: tl -> perms.owner <- true; process tl
      | Str "group" :: tl -> perms.group <- true; process tl
      | Str "other" :: tl -> perms.other <- true; process tl
      | v :: _ -> Error (Printf.sprintf "Unknown permission for: %s"
                                        (ParseTree.unparse_val v))
    in process vs

  let extract_file_perms (args: args) : (Ast.file_perms, string) result =
    let read =
      match extract_arg args "read" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_file_perm vs)
    in let write =
      match extract_arg args "write" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_file_perm vs)
    in let exec =
      match extract_arg args "execute" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_file_perm vs)
    in let file_list =
      match extract args [Str "list"; Str "files"] with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_file_perm vs)
    in let setuid =
      match extract_arg args "setuid" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_bool vs)
    in let setgid =
      match extract_arg args "setgid" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_bool vs)
    in let sticky =
      match extract_arg args "sticky" with
      | None -> Ok None
      | Some vs -> Result.map Option.some (extract_bool vs)
    in Result.bind read (fun read ->
        Result.bind write (fun write ->
          Result.bind exec (fun exec ->
            Result.bind file_list (fun file_list ->
              Result.bind setuid (fun setuid ->
                Result.bind setgid (fun setgid ->
                  Result.bind sticky (fun sticky ->
                    Ok { Ast.read = read; write = write; exec = exec;
                         file_list = file_list; setuid = setuid;
                         setgid = setgid; sticky = sticky })))))))

  let extract_file_info (args: args) : (file_info, string) result =
    let owner =
      match extract_arg args "owner" with
      | None -> Ok None
      | Some [v] -> Ok (Some v)
      | Some vs ->
          Error (Printf.sprintf "Expected single value for 'owner', found: %s"
                    (ParseTree.unparse_vals vs))
    in let group =
      match extract_arg args "group" with
      | None -> Ok None
      | Some [v] -> Ok (Some v)
      | Some vs ->
          Error (Printf.sprintf "Expected single value for 'group', found: %s"
                    (ParseTree.unparse_vals vs))
    in Result.bind owner (fun owner ->
        Result.bind group (fun group ->
          Result.bind (extract_file_perms args) (fun perms ->
            Ok { owner = owner; group = group; perms = perms })))

  let rec analyze_conditional (ctx: context) (c: ParseTree.cond)
    (t: ParseTree.base) (e: ParseTree.base)
    : (Ast.query, string) result =
    match c with
    | And (x, y) -> analyze_conditional ctx x (If (y, t, e)) e
    | Or (x, y) -> analyze_conditional ctx x t (If (y, t, e))
    | Not c -> analyze_conditional ctx c e t
    | Eq (lhs, rhs) ->
        if lhs = ([Str "os"], [])
        then let os : (Ast.ansible_os, string) result =
          match rhs with
          | ([Str "Debian"], []) -> Ok Debian
          | ([Str "Ubuntu"], []) -> Ok Ubuntu
          | ([Str "RedHat"], []) -> Ok RedHat
          | _ -> Error (Printf.sprintf "Unknown OS: %s"
                                       (ParseTree.unparse_expr rhs))
        in Result.bind os (fun os ->
          Result.bind (analyze_base (refine_context_os ctx os) t) (fun t ->
            Result.bind (analyze_base (refine_context_not_os ctx os) e)
              (fun e -> Ok (Ast.Cond (Ast.CheckOs os, t, e)))))
        else Error (Printf.sprintf "Unhandled equality check between %s and %s"
                     (ParseTree.unparse_expr lhs) (ParseTree.unparse_expr rhs))
    | Exists desc ->
        begin match desc with
        | (Str "file" :: path, []) | ([Str "file"], [([Str "at"], path)]) ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.FileExists p, t, e)))))
        | (Str "directory" :: path, [])
        | ([Str "directory"], [([Str "at"], path)]) ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.DirExists p, t, e)))))
        | (desc, args) ->
            let args = make_args args
            in let (last, rest) = list_last desc
            in match last with
            | Str "file" ->
                Result.bind (Knowledge.fileDef ctx rest args) (fun p ->
                  if args_empty args
                  then
                    Result.bind (analyze_base ctx t) (fun t ->
                      Result.bind (analyze_base ctx e) (fun e ->
                        Ok (Ast.Cond (Ast.FileExists p, t, e))))
                  else
                    Error (Printf.sprintf "Unhandled arguments in exists: %s"
                                          (args_to_string args)))
            | Str "directory" ->
                Result.bind (Knowledge.dirDef ctx rest args) (fun p ->
                  if args_empty args
                  then
                    Result.bind (analyze_base ctx t) (fun t ->
                      Result.bind (analyze_base ctx e) (fun e ->
                        Ok (Ast.Cond (Ast.DirExists p, t, e))))
                  else
                    Error (Printf.sprintf "Unhandled arguments in exists: %s"
                                          (args_to_string args)))
            | _ -> Error (Printf.sprintf "cannot check existance of: %s"
                            (ParseTree.unparse_vals desc))
        end
    | Required (desc, args) ->
        let args = make_args args
        in Result.bind (Knowledge.requirementDef ctx desc args) (fun c ->
            if args_empty args
            then
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (c, t, e))))
            else
              Error (Printf.sprintf "Unhandled arguments in required: %s"
                                    (args_to_string args)))
    | Installed (desc, args) ->
        let args = make_args args
        in Result.bind (Knowledge.pkgDef ctx desc args) (fun pkg ->
          if args_empty args
          then
            Result.bind (analyze_base ctx t) (fun t ->
              Result.bind (analyze_base ctx e) (fun e ->
                Ok (Ast.Cond (PkgInstalled pkg, t, e))))
          else
            Error (Printf.sprintf "Unhandled arguments in installed: %s"
                                  (args_to_string args)))
    | Running (desc, args) ->
        let args = make_args args
        in Result.bind (Knowledge.serviceDef ctx desc args) (fun nm ->
          if args_empty args
          then
            Result.bind (analyze_base ctx t) (fun t ->
              Result.bind (analyze_base ctx e) (fun e ->
                Ok (Ast.Cond (ServiceRunning nm, t, e))))
          else
            Error (Printf.sprintf "Unhandled arguments in running: %s"
                                  (args_to_string args)))

  and analyze_atom (ctx: context) (a: ParseTree.atom)
    : (Ast.act, string) result =
    let (act, args) = a
    in let args = make_args args
    in match act with
    | Clone vs ->
        let (last, rest) = list_last vs
        in if last = Str "repository"
        then Result.bind (Knowledge.gitRepoDef ctx rest args) (fun repo ->
          match extract_arg args "into" with
          | None -> Error "Clone requires 'into' argument with target directory"
          | Some p -> Result.bind (analyze_path p) (fun p ->
              Result.bind (extract_file_info args) (fun file_info ->
                if args_empty args
                then 
                  Ok (Ast.CloneGitRepo {
                      repo = repo.repo; version = repo.version;
                      dest = { path = p; owner = file_info.owner;
                               group = file_info.group;
                               perms = file_info.perms }})
                else Error (Printf.sprintf "Unhandled arguments for clone: %s"
                                            (args_to_string args)))))
        else Error (Printf.sprintf "Unsure how to clone: %s"
                      (ParseTree.unparse_vals vs))
    | Copy vs ->
        let (last, rest) = list_last vs
        in let rest_consumed = ref false
        in begin match last with
        | Str ("file" as ty) | Str ("directory" as ty) ->
            let (def, codegen) =
              if ty = "file"
              then (Knowledge.fileDef,
                    fun src dst -> Ast.CopyFile { src = src; dest = dst })
              else (Knowledge.dirDef,
                    fun src dst -> Ast.CopyDir { src = src; dest = dst })
            in let src =
              match extract_arg args "from" with
              | Some p -> analyze_path p
              | None -> rest_consumed := true; def ctx rest args
            in let dst =
              match extract_arg args "to" with
              | Some p -> analyze_path p
              | None -> if !rest_consumed
                  then Error "For copy, expected at least one of 'to' and 'from'"
                  else (rest_consumed := true; def ctx rest args)
            in if not !rest_consumed && not (List.is_empty rest)
            then Error (Printf.sprintf "Copy description not used: %s"
                                       (ParseTree.unparse_vals rest))
            else Result.bind src (fun src ->
                  Result.bind dst (fun dst ->
                    Result.bind (extract_file_info args) (fun file_info ->
                      if args_empty args
                      then Ok (codegen src
                                  { path = dst; owner = file_info.owner;
                                    group = file_info.group;
                                    perms = file_info.perms })
                      else 
                        Error (Printf.sprintf "Unhandled arguments for copy: %s"
                                              (args_to_string args)))))
        | Str "files" ->
            let src =
              match extract_arg args "from" with
              | None -> rest_consumed := true; Knowledge.filesDef ctx rest args
              | Some p -> Result.bind (analyze_path p) (fun p ->
                  match extract_arg args "glob" with
                  | None -> Ok (Ast.InPath p)
                  | Some [Str glob] -> Ok (Glob { base = p; glob = glob })
                  | Some vs ->
                      Error (Printf.sprintf
                            "Expected a single string as file glob, found: %s"
                            (ParseTree.unparse_vals vs)))
            in let dst =
              match extract_arg args "to" with
              | Some p -> Result.map (fun p -> Ast.InPath p) (analyze_path p)
              | None -> if !rest_consumed
                  then Error "For copy, expected at least one of 'to' and 'from'"
                  else (rest_consumed := true; Knowledge.filesDef ctx rest args)
            in if not !rest_consumed && not (List.is_empty rest)
            then Error (Printf.sprintf "Copy description not used: %s"
                                       (ParseTree.unparse_vals rest))
            else
              Result.bind src (fun src ->
                Result.bind dst (fun dst ->
                  Result.bind (extract_file_info args) (fun file_info ->
                    if args_empty args
                    then Ok (Ast.CopyFiles { src = src;
                      dest = { paths = dst; owner = file_info.owner;
                               group = file_info.group;
                               perms = file_info.perms }})
                    else
                      Error (Printf.sprintf "Unhandled arguments for copy: %s"
                                            (args_to_string args)))))
        | _ -> Error (Printf.sprintf "Unhandled copy of: %s"
                                     (ParseTree.unparse_vals vs))
        end
    | Create vs ->
        let (last, rest) = list_last vs
        in begin match last with
        | Str "file" ->
            let path =
              match extract_arg args "at" with
              | Some p -> if List.is_empty rest then analyze_path p
                  else Error (Printf.sprintf
                        "For create, argument 'at' should not be mixed with file description '%s'"
                        (ParseTree.unparse_vals rest))
              | None -> Knowledge.fileDef ctx rest args
            in let contents =
              match extract_arg args "content" with
              | None -> Ok None
              | Some [Str s] -> Ok (Some s) 
              | Some vs ->
                  Error (Printf.sprintf
                        "Expected a single string as file content, found: %s"
                        (ParseTree.unparse_vals vs))
            in Result.bind path (fun path ->
                Result.bind contents (fun contents ->
                  Result.bind (extract_file_info args) (fun file_info ->
                    if args_empty args
                    then Ok (Ast.CreateFile { 
                              dest= { path = path; owner = file_info.owner;
                                      group = file_info.group;
                                      perms = file_info.perms };
                              content = contents })
                    else
                      Error (Printf.sprintf "Unhandled arguments for create directory: %s"
                                            (args_to_string args)))))
        | Str "directory" ->
            let path =
              match extract_arg args "at" with
              | Some p -> if List.is_empty rest then analyze_path p
                  else Error (Printf.sprintf
                        "For create, argument 'at' should not be mixed with directory description '%s'"
                        (ParseTree.unparse_vals rest))
              | None -> Knowledge.dirDef ctx rest args
            in Result.bind path (fun path ->
                Result.bind (extract_file_info args) (fun file_info ->
                  if args_empty args
                  then Ok (Ast.CreateDir {
                            dest = { path = path; owner = file_info.owner;
                                     group = file_info.group;
                                     perms = file_info.perms } })
                  else
                    Error (Printf.sprintf "Unhandled arguments for create directory: %s"
                                          (args_to_string args))))
        | Str "user" ->
            if not (List.is_empty rest)
            then Error (Printf.sprintf "Unhandled user description in create: %s"
                                       (ParseTree.unparse_vals vs))
            else let name =
              match extract_arg args "name" with
              | None -> Error "Argument 'name' is required to create user"
              | Some [Str s] -> Ok s
              | Some vs ->
                  Error (Printf.sprintf
                          "Expected a single string as user name, found: %s"
                          (ParseTree.unparse_vals vs))
            in let group =
              match extract_arg args "group" with
              | None -> Ok None
              | Some [Str s] -> Ok (Some s)
              | Some vs ->
                  Error (Printf.sprintf
                          "Expected a single string as user group, found: %s"
                          (ParseTree.unparse_vals vs))
            in let groups =
              match extract_arg args "groups" with
              | None -> Ok None
              | Some nms ->
                  Result.bind 
                    (map_result
                      (fun nm -> match nm with ParseTree.Str n -> Ok n 
                        | _ -> Error (Printf.sprintf 
                            "Expected group names to be strings, found: %s"
                            (ParseTree.unparse_val nm)))
                      nms)
                    (fun groups -> Ok (Some groups))
            in Result.bind name (fun name ->
                Result.bind group (fun group ->
                  Result.bind groups (fun groups ->
                    if args_empty args
                    then Ok (Ast.CreateUser { name = name; group = group;
                                              groups = groups })
                    else Error (Printf.sprintf
                            "Unhandled arguments for create user: %s"
                            (args_to_string args)))))
        | Str "group" ->
            if not (List.is_empty rest)
            then Error (Printf.sprintf "Unhandled group description in create: %s"
                                       (ParseTree.unparse_vals vs))
            else let name =
              match extract_arg args "name" with
              | None -> Error "Argument 'name' is required to create group"
              | Some [Str s] -> Ok s
              | Some vs ->
                  Error (Printf.sprintf
                          "Expected a single string as group name, found: %s"
                          (ParseTree.unparse_vals vs))
            in Result.bind name (fun name ->
              if args_empty args
              then Ok (Ast.CreateGroup { name = name })
              else Error (Printf.sprintf "Unhandled arguments for create group: %s"
                                         (args_to_string args)))
        (* TODO: Not certain this shouldn't be part of the knowledge base,
         * this is assuming "virtual environment" is always a python env but
         * it could be used for other systems as well *)
        | Str "environment" ->
            begin match rest with
            | [Str "virtual"] ->
                let path =
                  match extract_arg args "in" with
                  | None -> Error "Argument 'in' is required to create virtual environment"
                  | Some p -> analyze_path p
                in let version =
                  match extract_arg args "python" with
                  | None -> Ok None
                  | Some [Str s] -> Ok (Some s)
                  | Some vs ->
                      Error (Printf.sprintf
                              "Expected a single string as python version, found: %s"
                              (ParseTree.unparse_vals vs))
                in Result.bind path (fun path ->
                    Result.bind version (fun version ->
                      if args_empty args
                      then Ok (Ast.CreateVirtualEnv { version = version; loc = path })
                      else Error (Printf.sprintf
                        "Unhandled arguments for create virtual environment: %s"
                        (args_to_string args))))
            | _ -> Error (Printf.sprintf
                            "Unhandled environment type for create: %s"
                            (ParseTree.unparse_vals rest))
            end
        (* TODO: Same as above, maybe other types of keys can be supported by
         * making this part of the knowledge base *)
        | Str "key" ->
            begin match rest with
            | [Str "ssh"] ->
                let user =
                  match extract_arg args "user" with
                  | None -> Error "Argument 'user' is required to create ssh key"
                  | Some [Str n] -> Ok n
                  | Some vs ->
                      Error (Printf.sprintf
                        "Expected a single string as user name for ssh key, found: %s"
                        (ParseTree.unparse_vals vs))
                in let path_at =
                  match extract_arg args "at" with
                  | Some p -> Result.map Option.some (analyze_path p)
                  | None -> Ok None
                in let path_name =
                  match extract_arg args "name" with
                  | None -> Ok None
                  | Some [Str n] ->
                      Result.bind user
                        (fun user -> 
                          Ok (Some (Ast.Remote (Str 
                            (Printf.sprintf "/home/%s/.ssh/%s" user n)))))
                  | Some vs ->
                      Error (Printf.sprintf
                        "Expected a single string as name for ssh key, found: %s"
                        (ParseTree.unparse_vals vs))
                in Result.bind user (fun user ->
                    Result.bind path_at (fun path_at ->
                      Result.bind path_name (fun path_name ->
                        if args_empty args
                        then
                          match path_at, path_name with
                          | Some path, None | None, Some path ->
                              Ok (Ast.CreateSshKey { user = user; loc = path })
                          | Some _, Some _ | None, None ->
                              Error "Expected exactly one of 'at' and 'name' arguments to create ssh key"
                        else
                          Error (Printf.sprintf
                            "Unhandled arguments for create ssh key: %s"
                            (args_to_string args)))))
            | _ -> Error (Printf.sprintf
                            "Unhandled key type for create: %s"
                            (ParseTree.unparse_vals rest))
            end
        | _ -> Error (Printf.sprintf "Unhandled creation of: %s"
                                     (ParseTree.unparse_vals vs))
        end
    | _ -> Error "TODO (S1)"

  and analyze_base (ctx: context) (b: ParseTree.base)
    : (Ast.query, string) result =
    match b with
    | Nil -> Ok End
    | Cons (a, b) ->
        Result.bind (analyze_atom ctx a) (fun a ->
          Result.bind (analyze_base ctx b) (fun b ->
            Ok (Ast.Seq (Atom a, b))))
    | If (c, t, e) -> analyze_conditional ctx c t e

  let rec analyze_top (q: ParseTree.top) : (Ast.query, string) result =
    match q with
    | [] -> Ok End
    | b :: q ->
        Result.bind (analyze_base init_context b) (fun b ->
          Result.bind (analyze_top q) (fun q ->
            Ok (Ast.Seq (b, q))))
end
