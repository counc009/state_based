module Target = Modules.Ast

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let ( let^ ) r f = Result.bind r f
let ( let$ ) r f = r f

type typ = Target.typ

type env = {
  unknowns: typ StringMap.t;
  users: StringSet.t;
  os: StringSet.t option
}

let env_empty : env = {
  unknowns = StringMap.empty;
  users = StringSet.empty;
  os = None;
}

let add_unknown (env : env) (nm : string) (ty : typ) : (env, string) result =
  let err = ref false
  in let map = StringMap.update nm (fun t ->
    match t with
    | None -> Some ty
    | Some t when t = ty -> Some ty
    | Some _ -> err := true; t) env.unknowns
  in if !err
  then Error (Printf.sprintf "Unknown '%s' used with different types" nm)
  else Ok { unknowns = map; users = env.users; os = env.os }

let add_user (env : env) (nm : string) : env =
  { unknowns = env.unknowns; users = StringSet.add nm env.users; os = env.os }

let add_os (env : env) (nm : string) : env =
  { unknowns = env.unknowns; users = env.users;
    os = match env.os with None -> Some (StringSet.singleton nm)
         | Some cur -> Some (StringSet.add nm cur) }

let codegen_value (v : ParseTree.value) (ty : typ) (env : env)
  (from_str : string -> Target.expr) : (Target.expr * env, string) result =
  match v with
  | Str s -> Ok (from_str s, env)
  | Unknown v ->
      let^ env = add_unknown env v ty
      in Ok (Target.Id ("?" ^ v), env)

let codegen_ast_value (v : Ast.value) (ty : typ) (env : env)
  (from_str : string -> Target.expr) : (Target.expr * env, string) result =
   match v with
   | Parsed v -> codegen_value v ty env from_str
   | Target e -> Ok (e, env)

(* Returns the path and system as expressions *)
let codegen_path (p : Ast.path) (env : env)
  : (Target.expr * Target.expr * env, string) result =
  let system =
    let sys = match p with Controller _ -> "local" | Remote _ -> "remote"
    in Target.EnumExp (Id "file_system", None, sys, [])
  in let^ (path, env) =
    match p with
    | Controller (Absolute v) | Remote (Absolute v) ->
        codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
    | Controller (InHome (user, v)) | Remote (InHome (user, v)) ->
        let user_exp = Target.FuncExp (Id "e_user", [StringLit user])
        in let^ (path, env) =
          codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
        in Ok (Target.FuncExp (Id "cons_path",
                  [ Field (user_exp, "homedir"); path ]),
                add_user env user)
  in Ok (path, system, env)

(* Returns the paths and system as expressions *)
let codegen_paths (p : Ast.paths) (env : env)
  : (Target.expr * Target.expr * env, string) result =
  match p with
  | InPath p ->
      let^ (p, sys, env) = codegen_path p env
      in Ok (Target.FuncExp (Id "get_dir_contents", [p; sys]), sys, env)
  | Glob { base; glob } ->
      (* NOTE: Really should change how globs work so that it works more
       * like the no glob case, but that'll require fixing other stuff *)
      let^ (p, sys, env) = codegen_path base env
      in let glob_expr =
        Target.FuncExp (Id "string_of_path",
          [ FuncExp (Id "cons_path", [ p; PathLit glob ]) ])
      in let globs =
        Target.EnumExp (Id "list", Some String, "cons",
          [ glob_expr; EnumExp (Id "list", Some String, "nil", []) ])
      in let paths =
        Target.FuncExp (Id "file_glob",
          [ globs; EnumExp (Id "find_file_type", None, "file", []); sys ])
      in Ok (paths, sys, env)

(* Given path and system expressions, returns an expression for the fs *)
let fs (p : Target.expr) (s : Target.expr) : Target.expr =
  FuncExp (Id "fs", [p; s])

(* Given a file permissions object, codegen setting the fs object's mode *)
let codegen_file_perms (fs : Target.expr) (p : Ast.file_perms)
  : Target.stmt list =
  let { Ast.read; write; exec; file_list; setuid; setgid; sticky } = p
  in let mode =
    (* The way we handle modes is to assume that if any permission information
     * is specified the remainder of information is specifically left out. *)
    let owner =
      let read = Option.fold read ~none:""
                                ~some:(fun (p : Ast.perm) -> 
                                      if p.owner then "r" else "")
      in let write = Option.fold write ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.owner then "w" else "")
      in let exec = Option.fold exec ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.owner then "x" else "")
      in let file_list = Option.fold file_list ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.owner && exec = "" then "X" else "")
      in let setuid = Option.fold setuid ~none:""
                                ~some:(fun p -> if p then "s" else "")
      in let perm = read ^ write ^ exec ^ file_list ^ setuid
      in if perm = "" then None else Some ("u=" ^ perm)
    in let group =
      let read = Option.fold read ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.group then "r" else "")
      in let write = Option.fold write ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.group then "w" else "")
      in let exec = Option.fold exec ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.group then "x" else "")
      in let file_list = Option.fold file_list ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.group && exec = "" then "X" else "")
      in let setgid = Option.fold setgid ~none:""
                                ~some:(fun p -> if p then "s" else "")
      in let perm = read ^ write ^ exec ^ file_list ^ setgid
      in if perm = "" then None else Some ("g=" ^ perm)
    in let other =
      let read = Option.fold read ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.other then "r" else "")
      in let write = Option.fold write ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.other then "w" else "")
      in let exec = Option.fold exec ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.other then "x" else "")
      in let file_list = Option.fold file_list ~none:""
                                ~some:(fun (p : Ast.perm) ->
                                      if p.other && exec = "" then "X" else "")
      in let sticky = Option.fold sticky ~none:""
                                ~some:(fun p -> if p then "t" else "")
      in let perm = read ^ write ^ exec ^ file_list ^ sticky
      in if perm = "" then None else Some ("o=" ^ perm)
    in let all =
      Option.to_list owner @ Option.to_list group @ Option.to_list other
    in let str = String.concat "," all
    in if str = "" then None else Some str
  in match mode with
  | None -> []
  | Some m -> Target.Assign (Field (fs, "mode"), StringLit m) :: []

let rec existential_cases (cs : Target.stmt list)
  : (Target.stmt, string) result =
  match cs with
  | [] -> Error "No cases"
  | [c] -> Ok c
  | c :: cs ->
      let^ cs = existential_cases cs
      in let cond : Target.expr =
        GenExistential (Bool, (fun _ -> Target.BoolLit true))
      in Ok (Target.IfThenElse (cond, [c], [cs]))

(* Given a file description code-gen setting the fs-object information *)
let codegen_file_info (fs : Target.expr) (owner : ParseTree.value option)
  (group : ParseTree.value option) (perms : Ast.file_perms) (env : env)
  : (Target.stmt list * env, string) result =
  let config_mode = codegen_file_perms fs perms
  in let^ (config_group, env) =
    match group with
    | None -> Ok (config_mode, env)
    | Some g ->
        let^ (group, env) =
          codegen_value g Target.String env (fun s -> StringLit s)
        in Ok (Target.Assign (Field (fs, "owner_group"), group) 
                :: config_mode, env)
  in match owner with
  | None -> Ok (config_group, env)
  | Some u ->
      let^ (user, env) =
        codegen_value u Target.String env (fun s -> StringLit s)
      in Ok (Target.Assign (Field (fs, "owner"), user) :: config_group, env)

let codegen_file_desc (fs : Target.expr) (p : Ast.file_desc) (env : env)
  : (Target.stmt list * env, string) result =
  let { Ast.path = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms env

let codegen_files_desc (fs : Target.expr) (p : Ast.files_desc) (env : env)
  : (Target.stmt list * env, string) result =
  let { Ast.paths = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms env

let codegen_condition (c: Ast.cond) (thn : Target.stmt list)
  (els : Target.stmt list) (env : env) : (Target.stmt * env, string) result =
  match c with
  | CheckOs os ->
      (* Ansible has (at least) two different variables that reflect what OS
       * we're running on. These are ansible_os_family and
       * ansible_distribution. The os_family reflects (for example) that
       * Ubuntu is Debian-based (so both Ubuntu and Debian have os_family
       * "Debian") while distribution differentiates between these OSes.
       * Because of this, if we are looking for a particular OS the condition
       * is over the distribution and then we assert about the family. We also
       * have DebianFamily and RedHatFamily OSes which just check the family *)
      begin match os with
      | Debian -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_distribution"),
              StringLit "Debian",
              Eq),
            Assert (
              BinaryExp (
                Field (FuncExp (Id "env", []), "os_family"),
                StringLit "Debian",
                Eq)) :: thn,
            els),
            add_os env "Debian")
      | RedHat -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_distribution"),
              StringLit "RedHat",
              Eq),
            Assert (
              BinaryExp (
                Field (FuncExp (Id "env", []), "os_family"),
                StringLit "RedHat",
                Eq)) :: thn,
            els),
            add_os env "RedHat")
      | Ubuntu -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_distribution"),
              StringLit "Ubuntu",
              Eq),
            Assert (
              BinaryExp (
                Field (FuncExp (Id "env", []), "os_family"),
                StringLit "Debian",
                Eq)) :: thn,
            els),
            add_os env "Debian")
      | DebianFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "Debian",
              Eq),
            thn,
            els),
            add_os env "Debian")
      | RedHatFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "RedHat",
              Eq),
            thn,
            els),
            add_os env "RedHat")
      end
  (* For file and directory exists we check the existance of the file-system
   * object and if it exists we assert it is a file/directory since normally
   * people don't check for the presence of a file/directory and expect to find
   * the other, they expect to either find what they expect or nothing *)
  | FileExists p ->
      let^ (path, system, env) = codegen_path p env
      in Ok (Target.IfExists (fs path system,
              Assert (FuncExp (Id "is_file", [path; system])) :: thn,
              els),
            env)
  | DirExists p ->
      let^ (path, system, env) = codegen_path p env
      in Ok (Target.IfExists (fs path system,
              Assert (FuncExp (Id "is_dir", [path; system])) :: thn,
              els),
            env)
  | PkgInstalled pkgs ->
      let^ (pkg_cases, env) =
        List.fold_left (fun acc { Ast.name; pkg_manager } ->
          let^ (pkg_cases, env) = acc
          in let^ (cond, env) =
            match pkg_manager with
            (* We only care about the package manager if it specifies a virtual
             * environment since that changes how we check whether it is
             * installed *)
            | System | Apt | Dnf | Pip None ->
                Ok (Target.FuncExp (Id "e_package", [StringLit name]), env)
            | Pip (Some p) ->
                let^ (path, env) =
                  codegen_value p Target.Path env (fun s -> PathLit s)
                in let virtenv =
                  Target.FuncExp (Id "virtual_environment", [path])
                in Ok (Target.FuncExp (Field (virtenv, "e_package"),
                    [StringLit name]), env)
          in Ok (Target.IfExists (cond, thn, els) :: pkg_cases, env)
        ) (Ok ([], env)) pkgs
      in let^ res = existential_cases pkg_cases
      in Ok (res, env)
  | ServiceRunning serv ->
      let service = Target.FuncExp (Id "e_service", [Id "^serv"])
      in Ok (
        Target.Seq (
          [LetStmt ("^serv", serv)],
          [IfExists (Id "^serv",
            [IfThenElse (Field (service, "running"), thn, els)],
            els)]),
        env)

let codegen_act (a : Ast.act) (env : env)
  : (Target.stmt list * env, string) result =
  match a with
  | CloneGitRepo { repo; version; dest } ->
      let^ (dir_path, sys, env) = codegen_path dest.path env
      in let^ (version, env) =
        match version with
        | None -> Ok (Target.StringLit "HEAD", env)
        | Some v ->
            codegen_value v Target.String env (fun s -> Target.StringLit s)
      in let files =
        Target.FuncExp (Id "git_files",
          [Id "^repo"; version; StringLit "origin"])
      in let^ (config_dir, env) =
        codegen_file_desc (fs (Id "^dst") sys) dest env
      in Ok (
        Target.LetStmt ("^repo", repo)
        :: LetStmt ("^dst", dir_path)
        :: Assign (Field (fs (Id "^dst") sys, "fs_type"),
            EnumExp (Id "file_type", None, "directory", [
              ForEachExp ("f", files,
                [ LetStmt ("p", FuncExp (Id "cons_path", [Id "^dst"; Id "f"]))
                ; Assign (Field (fs (Id "p") sys, "fs_type"),
                    EnumExp (Id "file_type", None, "file", [
                      FuncExp (Id "git_content",
                        [Id "^repo"; version; StringLit "origin"; Id "f"])
                    ]))
                ; Yield (Id "p") ]) ]))
        :: config_dir, env)
  | CopyDir { src; dest } ->
      let^ (src_path, src_sys, env) = codegen_path src env
      in let^ (dst_path, dst_sys, env) = codegen_path dest.path env
      in let^ (config_dst, env) = 
        codegen_file_desc (fs (Id "^dst") dst_sys) dest env
      in Ok (
        Target.LetStmt ("^src", src_path)
        :: LetStmt ("^dst", dst_path)
        :: AssertExists (fs (Id "^src") src_sys)
        :: Assert (FuncExp (Id "is_dir", [Id "^src"; src_sys]))
        :: LetStmt ("files",
            ForEachExp (
              "file",
              FuncExp (Id "get_dir_contents", [Id "^src"; src_sys]),
              [ AssertExists (fs (Id "file") src_sys)
              ; Assert (FuncExp (Id "is_file", [Id "file"; src_sys]))
              ; LetStmt ("res",
                  FuncExp (Id "cons_path", [Id "^dst";
                    FuncExp (Id "path_from", [Id "^src"; Id "file"])]))
              ; Assign (Field (fs (Id "res") dst_sys, "fs_type"),
                        Field (fs (Id "file") src_sys, "fs_type"))
              ; Yield (Id "res") ]))
        :: Assign (Field (fs (Id  "^dst") dst_sys, "fs_type"),
                   EnumExp (Id "file_type", None, "directory",
                            [Id "files"]))
        :: config_dst, env)
  | CopyFile { src; dest } ->
      let^ (src_path, src_sys, env) = codegen_path src env
      in let^ (dst_path, dst_sys, env) = codegen_path dest.path env
      in let^ (config_dst, env) =
        codegen_file_desc (fs (Id "^dst") dst_sys) dest env
      in Ok (
        Target.LetStmt ("^src", src_path)
        :: LetStmt ("^dst", dst_path)
        :: AssertExists (fs (Id "^src") src_sys)
        :: Assert (FuncExp (Id "is_file", [Id "^src"; src_sys]))
        :: Assign (Field (fs (Id "^dst") dst_sys, "fs_type"),
                   Field (fs (Id "^src") src_sys, "fs_type"))
        :: config_dst, env)
  | CopyFiles { src; dest } ->
      let^ (src_paths, src_sys, env) = codegen_paths src env
      in begin match dest.paths with
      | Glob _ -> Error "Cannot copy into a glob"
      | InPath dst ->
          let^ (dst_path, dst_sys, env) = codegen_path dst env
          in let dst_file =
            Target.FuncExp (Id "cons_path",
              [ Id "^dst"; FuncExp (Id "base_name", [Id "f"]) ])
          in let^ (config_dst, env) = 
            codegen_files_desc (fs dst_file dst_sys) dest env
          in Ok (
            Target.LetStmt ("^dst", dst_path)
            :: ForLoop ("f", src_paths,
              Assert (FuncExp (Id "is_file", [Id "f"; src_sys]))
              :: Assign (Field (fs dst_file dst_sys, "fs_type"),
                  Field (fs (Id "f") src_sys, "fs_type"))
              :: config_dst
            ) :: [], env)
      end
  | CreateDir { dest } ->
      let^ (path, sys, env) = codegen_path dest.path env
      in let^ (config, env) = codegen_file_desc (fs (Id "^dst") sys) dest env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: Assign (
          Field (fs (Id "^dst") sys, "fs_type"),
          EnumExp (Id "file_type", None, "directory",
            [EnumExp (Id "list", Some Path, "nil", [])]))
        :: config, env)
  | CreateFile { dest; content } ->
      (* We assume that if you just say to create a file you want it to be
       * empty *)
      let content = Option.value ~default:"" content
      in let^ (path, sys, env) = codegen_path dest.path env
      in let^ (config, env) = codegen_file_desc (fs (Id "^dst") sys) dest env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: Assign (
          Field (fs (Id "^dst") sys, "fs_type"),
          EnumExp (Id "file_type", None, "file",
            [StringLit content]))
        :: config, env)
  | CreateGroup { name } ->
      Ok ([Target.Touch (FuncExp (Id "e_group", [StringLit name]))],
          env)
  (* NOTE: We should add options for key-type and probably other fields *)
  | CreateSshKey { loc } ->
      let^ (path, sys, env) = codegen_path loc env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: LetStmt ("time", GenExistential (Int, fun _ -> BoolLit true))
        :: Target.LetStmt ("comment",
            GenExistential (String, fun _ -> BoolLit true))
        :: Assign (Field (fs (Id "^dst") sys, "fs_type"),
            EnumExp (Id "file_type", None, "file",
              [ FuncExp (Id "ssh_private_key",
                [ StringLit "rsa"
                ; FuncExp (Id "default_ssh_key_bits", [])
                ; EnumExp (Id "option", Some String, "nothing", [])
                ; Id "comment"
                ; Id "time" ]) ]))
        :: Assign (
            Field (
              fs (FuncExp (Id "add_ext", [Id "^dst"; StringLit ".pub"])) sys, 
              "fs_type"),
            EnumExp (Id "file_type", None, "file",
              [ FuncExp (Id "ssh_public_key",
                [ StringLit "rsa"
                ; FuncExp (Id "default_ssh_key_bits", [])
                ; EnumExp (Id "option", Some String, "nothing", [])
                ; Id "comment"
                ; Id "time" ]) ]))
        :: [], env)
  | CreateUser { name; group; groups } ->
      let user = Target.FuncExp (Id "e_user", [StringLit name])
      in let res_groups =
        match groups with
        | None -> []
        | Some groups ->
            let groups = List.map (fun s -> Target.StringLit s) groups
            in let groups =
              List.fold_left
                (fun ex g ->
                  Target.EnumExp (Id "list", Some String, "cons", [g; ex]))
                (Target.EnumExp (Id "list", Some String, "nil", []))
                groups
            in Target.Assign(Target.Field(user, "supplemental_groups"), groups)
            :: []
      in let res_group =
        match group with
        | None -> res_groups
        | Some group ->
            Target.Assign (Target.Field (user, "primary_group"), StringLit group)
            :: res_groups
      in Ok (Target.Touch user :: res_group, env)
  | CreateVirtualEnv { version; loc } ->
      let^ (path, env) =
        match loc with
        | Controller _ ->
            Error "Virtual Environment must be on remote machine"
        | Remote (Absolute v) ->
            codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
        | Remote (InHome (user, v)) ->
            let^ (path, env) =
              codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
            in Ok (
              Target.FuncExp (Id "cons_path", [
                Field (FuncExp (Id "e_user", [StringLit user]), "homedir");
                  path ]), env)
      in let virtenv = Target.FuncExp (Id "virtual_environment", [path])
      in let with_version =
        match version with
        | None -> Target.Touch virtenv
        | Some s -> 
            Target.Assign (Field (virtenv, "python_version"),
                           StringLit ("python" ^ s))
      in Ok ([with_version], env)
  | DeleteDir { loc } ->
      let^ (path, sys, env) = codegen_path loc env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: ForLoop ("f", FuncExp (Id "get_dir_contents", [Id "^dst"; sys]),
          [Clear (fs (Id "f") sys)])
        :: Clear (fs (Id "^dst") sys) :: [], env)
  | DeleteFile { loc } ->
      let^ (path, sys, env) = codegen_path loc env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: Assert (FuncExp (Id "is_file", [Id "^dst"; sys]))
        :: Clear (fs (Id "^dst") sys) :: [], env)
  | DeleteFiles { loc } ->
      begin match loc with
      | InPath p ->
          let^ (p, sys, env) = codegen_path p env
          in Ok (
            Target.LetStmt ("^dst", p)
            :: ForLoop ("f", FuncExp (Id "get_dir_contents", [Id "^dst"; sys]),
              [ Assert (FuncExp (Id "is_file", [Id "f"; sys]))
              ; Clear (fs (Id "f") sys) ])
          (* TODO: To ensure we can't just delete the directory, I have to add
           * this. Not sure how I feel about it *)
            :: Assign (Field (fs (Id "^dst") sys, "fs_type"),
                EnumExp (Id "file_type", None, "directory",
                  [EnumExp (Id "list", Some Path, "nil", [])]))
            :: [], env)
      | _ ->
          let^ (paths, sys, env) = codegen_paths loc env
          in Ok (Target.ForLoop ("f", paths,
                [ Assert (FuncExp (Id "is_file", [Id "f"; sys]))
                ; Clear (fs (Id "f") sys) ]) :: [], env)
      end
  | DeleteGroup { name } -> Ok (
      Target.Clear (FuncExp (Id "e_group", [StringLit name])) :: [],
      env)
  | DeleteUser { name } -> Ok (
      Target.Clear (FuncExp (Id "e_user", [StringLit name])) :: [],
      env)
  | DisablePassword { user } -> Ok (
      Target.Assign (Field (FuncExp (Id "e_user", [StringLit user]), "password"),
                     EnumExp (Id "password_set", None, "disabled", []))
      :: [], env)
  (* NOTE: I think it would be better to handle enable and disable of sudo by
   * setting the sudoers file's contents to a unknown value and then asserting
   * about it containing certain lines, but that requires interpreted functions
   * for reasoning about whether lines are contained in a string *)
  (* FIXME TODO: Support sudoers.d & other regexes *)
  | DisableSudo { who; passwordless } ->
      let user =
        match who with
        | User name -> name
        | Group name -> "%" ^ name
      in let path = Target.PathLit "/etc/sudoers"
      in let sys = Target.EnumExp (Id "file_system", None, "remote", [])
      in if passwordless
      then Ok (
        Target.LetStmt ("c", FuncExp (Id "get_file_content", [path; sys]))
        :: Target.IfThenElse ( (* FIXME: this regex *)
              FuncExp (Id "line_matches_regex",
                [ StringLit ("^" ^ user ^ ".*NOPASSWD"); Id "c" ]),
              [ LetStmt ("r",
                  FuncExp (Id "replace_last_matching", 
                    [ StringLit ("^" ^ user ^ ".*NOPASSWD")
                    ; StringLit (user ^ "\t" ^ "ALL=(ALL:ALL) ALL")
                    ; Id "c" ]))
              ; Assert (FuncExp (Id "validate_contents",
                  [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
              ; Assign (Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file", [Id "r"]))
              ],
              [])
        :: [], env)
      else Ok (
        Target.LetStmt ("c", FuncExp (Id "get_file_content", [path; sys]))
        (* "^" ^ user is only valid as the regex as long as user doesn't
         * contain any regular expression special characters *)
        :: LetStmt ("r", FuncExp (Id "remove_matching_lines", 
            [ StringLit ("^" ^ user); Id "c" ]))
        :: Assert (FuncExp (Id "validate_contents",
            [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
        :: Assign (Field (fs path sys, "fs_type"),
            EnumExp (Id "file_type", None, "file", [ Id "r" ]))
        :: [], env)
  | DownloadFile { dest; src } ->
      let^ (path, sys, env) = codegen_path dest.path env
      in let^ (config, env) = codegen_file_desc (fs (Id "^dst") sys) dest env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: Assign (
          Field (fs (Id "^dst") sys, "fs_type"),
          EnumExp (Id "file_type", None, "file",
            [FuncExp (Id "download_url",
              [PathLit src;
                EnumExp (Id "option",
                  Some (Product [String; String]), "nothing", [])])]))
       :: config, env)
  (* FIXME TODO: As above *)
  (* It's actually a non-trivial question of what it means to grant a user sudo
   * access, because you might only grant them access on certain machines, to
   * run certain commands, and they may only be able to run commands as certain
   * users/groups. In a more complete FQL these would probably be options to
   * the query.
   * For the moment, we assume that it means full sudo access, in other words
   * any machine, any user and group, and any command. *)
  | EnableSudo { who; passwordless } ->
      let user =
        match who with
        | User name -> name
        | Group name -> "%" ^ name
      in let line =
        let spec = "ALL=(ALL:ALL)"
        in let cmd = if passwordless then "NOPASSWD:ALL" else "ALL"
        (* TODO: The spacing of this line doesn't actually matter *)
        in Target.StringLit (user ^ "\t" ^ spec ^ " " ^ cmd)
      (* TODO: We should really be tracking information about how we want to
       * manage sudoers on the system, as that may impact what the path name
       * really should be. Some of the generated code also just creates the
       * file which could only be okay if we track those details to decide
       * whether overriding the file is fine. *)
      in let path =
        Target.GenExistential (Target.Path, fun nm ->
          BinaryExp (
            BinaryExp (
              Id nm,
              PathLit "/etc/sudoers",
              Eq
            ),
            BinaryExp (
              Id nm,
              FuncExp (Id "cons_path",
                [PathLit "/etc/sudoers.d";
                  GenExistential (Target.Path, fun _ -> BoolLit true)]),
              Eq
            ),
            Or))
      in let sys = Target.EnumExp (Id "file_system", None, "remote", [])
      (* Any of the regexes ^user, ^user.*, and ^user.*$ will work *)
      in let regex =
        (* Technically user could have special characters that need to be
         * escaped for a regex, but this is unlikely since the standard regex
         * for user names is ^[a-z][-a-z0-9]*$ *)
        let base_regex = "^" ^ user
        in Target.GenExistential (Target.String, fun nm ->
          BinaryExp (
            BinaryExp (Id nm, StringLit base_regex, Eq),
          BinaryExp (
            BinaryExp (Id nm, StringLit (base_regex ^ ".*"), Eq),
            BinaryExp (Id nm, StringLit (base_regex ^ ".*$"), Eq),
            Or),
          Or))
      in Ok (
        Target.LetStmt ("^path", path)
        :: LetStmt ("^regex", regex)
        :: LetStmt ("^line", line)
        :: LetStmt ("c", FuncExp (Id "get_file_content", [Id "^path"; sys]))
        :: Target.IfThenElse (
            FuncExp (Id "line_matches_regex", [ Id "^regex"; Id "c" ]),
            [ LetStmt ("r",
                FuncExp (Id "replace_last_matching", 
                  [ Id "^regex"; Id "^line"; Id "c" ]))
            ; Assert (FuncExp (Id "validate_contents",
                [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
            ; Assign (Field (fs (Id "^path") sys, "fs_type"),
                EnumExp (Id "file_type", None, "file", [Id "r"]))
            ],
            [ LetStmt ("r",
                FuncExp (Id "concat_line", [Id "c"; Id "^line"]))
            ; Assert (FuncExp (Id "validate_contents",
                [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
            ; Assign (Field (fs (Id "^path") sys, "fs_type"),
                EnumExp (Id "file_type", None, "file", [Id "r"]))
            ])
        :: [], env)
  | InstallPkg { pkg = pkgs; version } ->
      let^ (pkg_cases, env) =
        List.fold_left (fun acc { Ast.name; pkg_manager } ->
          let^ (cases, env) = acc
          in let^ (install, pkg, env) =
            match pkg_manager with
            | Apt ->
                let pkg = Target.FuncExp (Id "e_package", [StringLit name])
                in let install =
                  Target.Touch (FuncExp (Field (pkg, "e_apt"), []))
                in Ok (install, pkg, env)
            | Dnf ->
                let pkg = Target.FuncExp (Id "e_package", [StringLit name])
                in let install =
                  Target.Touch (FuncExp (Field (pkg, "e_dnf"), []))
                in Ok (install, pkg, env)
            | Pip None ->
                let pkg = Target.FuncExp (Id "e_package", [StringLit name])
                in let install =
                  Target.Touch (FuncExp (Field (pkg, "e_pip"), []))
                in Ok (install, pkg, env)
            | System ->
                let pkg = Target.FuncExp (Id "e_package", [StringLit name])
                in let os = Target.Field (FuncExp (Id "env", []), "os_family")
                in let install =
                  Target.IfThenElse (BinaryExp (os, StringLit "Debian", Eq),
                    [ Touch (FuncExp (Field (pkg, "e_apt"), [])) ],
                    [ IfThenElse (BinaryExp (os, StringLit "RedHat", Eq),
                      [ Touch (FuncExp (Field (pkg, "e_dnf"), [])) ],
                      [ Touch (FuncExp (Field (pkg, "sys"), [])) ]
                    )]
                  )
                in Ok (install, pkg, env)
            | Pip (Some p) ->
                let^ (path, env) =
                  codegen_value p Target.Path env (fun s -> PathLit s)
                in let virtenv =
                  Target.FuncExp (Id "virtual_environment", [Id "^dst"])
                in let pkg : Target.expr =
                  FuncExp (Field (virtenv, "e_package"), [StringLit name])
                in let install =
                  Target.Touch (FuncExp (Field (pkg, "e_pip"), []))
                in Ok (Target.Seq ([LetStmt ("^dst", path)], [install]),
                    pkg, env)
          in let full_install =
            match version with
            | None -> install
            | Some "latest" ->
                Target.Seq ([install],
                  [Assign (Field (pkg, "version"),
                    EnumExp (Id "package_version", None, "latest", []))])
            | Some v ->
                Target.Seq ([install],
                  [Assign (Field (pkg, "version"),
                    EnumExp (Id "package_version", None, "specific",
                      [StringLit v]))])
          in Ok (full_install :: cases, env)
        ) (Ok ([], env)) pkgs
      in let^ res = existential_cases pkg_cases
      in Ok ([res], env)
  | MoveDir { src; dest } ->
      let^ (src_path, src_sys, env) = codegen_path src env
      in let^ (dst_path, dst_sys, env) = codegen_path dest.path env
      in let^ (config, env) =
        codegen_file_desc (fs (Id "^dst") dst_sys) dest env
      in Ok (
        Target.LetStmt ("^src", src_path)
        :: LetStmt ("^dst", dst_path)
        :: AssertExists (fs (Id "^src") src_sys)
        :: Assert (FuncExp (Id "is_dir", [Id "^src"; src_sys]))
        :: LetStmt ("files",
            ForEachExp (
              "file",
              FuncExp (Id "get_dir_contents", [Id "^src"; src_sys]),
              [ AssertExists (fs (Id "file") src_sys)
              ; Assert (FuncExp (Id "is_file", [Id "file"; src_sys]))
              ; LetStmt ("res",
                  FuncExp (Id "cons_path", [Id "^dst";
                    FuncExp (Id "path_from", [Id "^src"; Id "file"])]))
              ; Assign (Field (fs (Id "res") dst_sys, "fs_type"),
                        Field (fs (Id "file") src_sys, "fs_type"))
              ; Clear (fs (Id "file") src_sys)
              ; Yield (Id "res") ]))
        :: Assign (Field (fs (Id "^dst") dst_sys, "fs_type"),
                   EnumExp (Id "file_type", None, "directory",
                            [Id "files"]))
        :: Clear (fs (Id "^src") src_sys)
        :: config, env)
  | MoveFile { src; dest } ->
      let^ (src_path, src_sys, env) = codegen_path src env
      in let^ (dst_path, dst_sys, env) = codegen_path dest.path env
      in let^ (config, env) =
        codegen_file_desc (fs (Id "^dst") dst_sys) dest env
      in Ok (
        Target.LetStmt ("^src", src_path)
        :: LetStmt ("^dst", dst_path)
        :: AssertExists (fs (Id "^src") src_sys)
        :: Assert (FuncExp (Id "is_file", [Id "^src"; src_sys]))
        :: Assign (Field (fs (Id "^dst") dst_sys, "fs_type"),
                    Field (fs (Id "^src") src_sys, "fs_type"))
        :: Clear (fs (Id "^src") src_sys)
        :: config, env)
  | MoveFiles { src; dest } ->
      let^ (src_paths, src_sys, env) = codegen_paths src env
      in begin match dest.paths with
      | Glob _ -> Error "Cannot move into a glob"
      | InPath dst ->
          let^ (dst_path, dst_sys, env) = codegen_path dst env
          in let dst_file =
            Target.FuncExp (Id "cons_path",
              [ Id "^dst"; FuncExp (Id "base_name", [Id "f"]) ])
          in let^ (config, env) = 
            codegen_files_desc (fs (Id "^dst") dst_sys) dest env
          in Ok (
            Target.LetStmt ("^dst", dst_path)
            :: ForLoop ("f", src_paths,
              Assert (FuncExp (Id "is_file", [Id "f"; src_sys]))
              :: Assign (Field (fs dst_file dst_sys, "fs_type"),
                  Field (fs (Id "f") src_sys, "fs_type"))
              :: Clear (fs (Id "f") src_sys)
              :: config)
            :: [], env)
      end
  | Reboot -> Ok (
    Target.LetStmt ("time", GenExistential (Int, fun _ -> BoolLit true))
    :: Assert (BinaryExp (IntLit 0, Id "time", Le))
    :: Assign (Field (FuncExp (Id "env", []), "last_reboot"), Id "time")
    :: [], env)
  (* FIXME TODO: Like with the sudoers file, I think it would be better to
   * assert about the result *)
  | SetEnvVar { name; value } ->
      let^ (value, env) =
        codegen_value value Target.String env (fun s -> StringLit s)
      in let path = Target.PathLit "/etc/environment"
      in let sys = Target.EnumExp (Id "file_system", None, "remote", [])
      in let regex =
        let base_regex = "^" ^ name ^ "="
        in Target.GenExistential (Target.String, fun nm ->
          BinaryExp (
            BinaryExp (Id nm, StringLit base_regex, Eq),
          BinaryExp (
            BinaryExp (Id nm, StringLit (base_regex ^ ".*"), Eq),
            BinaryExp (Id nm, StringLit (base_regex ^ ".*$"), Eq),
            Or),
          Or))
      in let line =
        Target.GenExistential (Target.String, fun nm ->
          BinaryExp (
            BinaryExp (Id nm, 
              BinaryExp(StringLit (name ^ "="), value, Concat), Eq),
            BinaryExp (Id nm,
              BinaryExp (BinaryExp (StringLit (name ^ "=\""), value, Concat), 
                StringLit "\"", Concat), Eq),
            Or))
      in let^ cases =
        (* Technically, it is fine to just always add the line to the end of
         * the file, so we handle two separate cases *)
        existential_cases [
          (* Option 1, search by regex and replace/add as appropriate *)
          Target.Seq ([],
            LetStmt ("^regex", regex)
            :: Target.IfThenElse (
              FuncExp (Id "line_matches_regex", [ Id "^regex"; Id "c" ]),
              [ LetStmt ("r",
                  FuncExp (Id "replace_last_matching",
                    [ Id "^regex"; Id "^line"; Id "c" ]))
              ; Assign (Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file", [Id "r"]))
              ],
              [ LetStmt ("r", FuncExp (Id "concat_line", [Id "c"; Id "^line"]))
              ; Assign (Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file", [Id "r"]))
              ])
            :: []);
          (* Option 2, just add it to the end of the file *)
          Target.Assign (Field (fs path sys, "fs_type"),
            EnumExp (Id "file_type", None, "file", [
              FuncExp (Id "concat_line", [Id "c"; Id "^line"])
            ]))
        ]
      in Ok (
        Target.LetStmt ("^line", line)
        :: LetStmt ("c", FuncExp (Id "get_file_content", [path; sys]))
        :: cases :: [], env)
  | SetFilePerms { loc; perms } ->
      let^ (path, sys, env) = codegen_path loc env
      in Ok (
        Target.LetStmt ("^dst", path)
        :: Assert (FuncExp (Id "is_file", [Id "^dst"; sys]))
        :: codegen_file_perms (fs (Id "^dst") sys) perms, env)
  | SetFilesPerms { locs; perms } ->
      let^ (paths, sys, env) = codegen_paths locs env
      in Ok (
        Target.ForLoop ("f", paths,
          Assert (FuncExp (Id "is_file", [Id "f"; sys]))
          :: codegen_file_perms (fs (Id "f") sys) perms)
        :: [], env)
  | SetShell { user; shell } ->
      let^ (shell, env) =
        match shell with
        | Controller _ -> Error "Path to a user's shell must be a remote path"
        | Remote (Absolute v) ->
            codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
        | Remote (InHome (user, v)) ->
            let^ (path, env) = 
              codegen_ast_value v Target.Path env (fun s -> Target.PathLit s)
            in Ok (
              Target.FuncExp (Id "cons_path",
                [ Field (FuncExp (Id "e_user", [StringLit user]), "homedir")
                ; path ]), env)
      in let user = Target.FuncExp (Id "e_user", [StringLit user])
      in Ok (Target.AssertExists user
              :: Assign (Field (user, "default_shell"), shell)
              :: [], env)
  | StartService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "e_service", [name]), "running"),
          BoolLit true) :: [], env)
  | StopService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "e_service", [name]), "running"),
          BoolLit false) :: [], env)
  | UninstallPkg { pkg = pkgs } ->
      let^ (pkg_cases, env) =
        List.fold_left (fun acc { Ast.name; pkg_manager } ->
          let^ (pkg_cases, env) = acc
          in let^ (uninstall, env) =
            match pkg_manager with
            | Apt | Dnf | Pip None | System ->
                let uninstall =
                  Target.Clear (FuncExp (Id "e_package", [StringLit name]))
                in Ok (uninstall, env)
            | Pip (Some p) ->
                let^ (path, env) =
                  codegen_value p Target.Path env (fun s -> Target.PathLit s)
                in let virtenv =
                  Target.FuncExp (Id "virtual_environment", [path])
                in let uninstall =
                  Target.Clear (FuncExp (Field (virtenv, "e_package"),
                    [StringLit name]))
                in Ok (uninstall, env)
          in Ok (uninstall :: pkg_cases, env)
        ) (Ok ([], env)) pkgs
      in let^ res = existential_cases pkg_cases
      in Ok ([res], env)
  | WriteFile { str; dest; position } ->
      let^ (path, sys, env) = codegen_path dest.path env
      in let^ (config, env) = codegen_file_desc (fs (Id "^dst") sys) dest env
      in let^ (str, env) =
        codegen_value str Target.String env (fun s -> Target.StringLit s)
      in let write =
        Target.LetStmt ("^dst", path)
        :: match position with
        | Overwrite ->
            Assign (Field (fs (Id "^dst") sys, "fs_type"),
              EnumExp (Id "file_type", None, "file", [str]))
            :: config
        | Top ->
            LetStmt ("c", FuncExp (Id "get_file_content", [Id "^dst"; sys]))
            :: Assign (Field (fs (Id "^dst") sys, "fs_type"),
                EnumExp (Id "file_type", None, "file",
                  [FuncExp (Id "concat_line", [str; Id "c"])]))
            :: config
        | Bottom ->
            LetStmt ("c", FuncExp (Id "get_file_content", [Id "^dst"; sys]))
            :: Assign (Field (fs (Id "^dst") sys, "fs_type"),
                EnumExp (Id "file_type", None, "file",
                  [FuncExp (Id "concat_line", [Id "c"; str])]))
            :: config
      in Ok (write, env)

let codegen_query (q : Ast.query) : (Target.stmt list, string) result =
  let rec codegen (q : Ast.query) (env : env)
    : (Target.stmt list * env, string) result =
    match q with
    | End -> Ok ([], env)
    | Atom act -> codegen_act act env
    | Seq (fst, snd) ->
        let^ (fst, env) = codegen fst env
        in let^ (snd, env) = codegen snd env
        in Ok ([Target.Seq (fst, snd)], env)
    | Cond (c, thn, els) ->
        let^ (thn, env) = codegen thn env
        in let^ (els, env) = codegen els env
        in let^ (res, env) = codegen_condition c thn els env
        in Ok ([res], env)
  in let^ (code, env) = codegen q env_empty
  in let setup =
    Target.AssertExists (FuncExp (Id "env", []))
    :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"), IntLit 0, Eq))
    :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "last_reboot"), IntLit (-1), Eq))
    (* TODO: Not sure this is ideal, but it at least makes sure we don't accept
     * solutions that are expected to work on multiple operating systems *)
    :: begin let os_families =
      match env.os with
      | None -> ["Debian"; "RedHat"]
      | Some os -> StringSet.elements os
    in Assert (List.fold_left (fun cond os ->
        Target.BinaryExp (
          BinaryExp (Field (FuncExp (Id "env", []), "os_family"), 
                     StringLit os, Eq),
          cond,
          Or)
      ) (BoolLit false) os_families)
    end
    :: code
  (* TODO: For the moment we're assuming that if a user already exists their
   * home directory is located at /home/NAME. Not sure this is ideal but a
   * lot of code will assume this (which is probably true 99% of the time)
   * which causes a bunch of challenges to make verification work. *)
  in let assert_users =
    StringSet.fold (fun user c ->
      let user_exp = Target.FuncExp (Id "e_user", [StringLit user])
      in Target.IfExists (user_exp,
        [ Assert (BinaryExp (
            Field (user_exp, "homedir"),
            PathLit (Printf.sprintf "/home/%s" user),
            Eq)) ],
        []) :: c
    ) env.users setup
  in let bind_unknowns =
    StringMap.fold (fun v t c ->
      Target.LetStmt ("?" ^ v, GenExistential (t, fun _ -> BoolLit true)) :: c
    ) env.unknowns assert_users
  in Ok bind_unknowns
