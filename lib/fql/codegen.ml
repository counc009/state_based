module Target = Modules.Ast

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type typ = Target.typ

type env = { unknowns: typ StringMap.t; users: StringSet.t }

let env_empty : env = { unknowns = StringMap.empty; users = StringSet.empty }

let add_unknown (env : env) (nm: string) (ty: typ)
  : (env, string) result =
  let err = ref false
  in let map = StringMap.update nm (fun t ->
    match t with
    | None -> Some ty
    | Some t when t = ty -> Some ty
    | Some _ -> err := true; t) env.unknowns
  in if !err
  then Error (Printf.sprintf "Unknown '%s' used with different types" nm)
  else Ok { unknowns = map; users = env.users }

let add_user (env: env) (nm: string) : env =
  { unknowns = env.unknowns; users = StringSet.add nm env.users }

let codegen_value (v: ParseTree.value) (ty: typ)
  (from_str: string -> Target.expr) env : (env * Target.expr, string) result =
  match v with
  | Str s -> Ok (env, from_str s)
  | Unknown v -> Result.bind (add_unknown env v ty) (fun map ->
      Ok (map, Target.Id ("?" ^ v)))

(* Returns the unknown map and then the path and system as expressions *)
let codegen_path (p: Ast.path) env
  : (env * Target.expr * Target.expr, string) result =
  let sys =
    match p with Controller _ -> "local" | Remote _ -> "remote"
  in let path =
    match p with
    | Controller (Value v) | Remote (Value v) ->
        codegen_value v Target.Path (fun s -> Target.PathLit s) env
    | Controller (InHome (user, v)) | Remote (InHome (user, v)) ->
        let user_exp = Target.FuncExp (Id "e_user", [StringLit user])
        in Result.bind
          (codegen_value v Target.Path (fun s -> Target.PathLit s) env)
          (fun (env, path) -> Ok (add_user env user,
            Target.FuncExp (Id "cons_path",
              [Field (user_exp, "homedir"); path])))
  in let system = Target.EnumExp (Id "file_system", None, sys, [])
  in Result.bind path (fun (map, path) -> Ok (map, path, system))

let codegen_paths (p: Ast.paths) env =
  match p with
  | InPath p ->
      Result.bind (codegen_path p env) (fun (map, p, sys) ->
        Ok (map, Target.FuncExp (Id "get_dir_contents", [p; sys]), sys))
  | Glob { base; glob } ->
      (* NOTE: Really should change how globs work so that it works more
       * like the no glob case, but that'll require fixing other stuff *)
      Result.bind (codegen_path base env) (fun (env, path, sys) ->
        let glob_expr =
          Target.FuncExp (Id "string_of_path",
            [ FuncExp (Id "cons_path", [ path; PathLit glob ]) ])
        in let globs = Target.EnumExp (Id "list", Some String, "cons",
                      [ glob_expr
                      ; EnumExp (Id "list", Some String, "nil", [])])
        in let paths = Target.FuncExp (Id "file_glob",
          [globs; EnumExp (Id "find_file_type", None, "file", [])
          ; sys])
        in Ok (env, paths, sys))

(* Given path and system expressions, returns an expression for the fs *)
let fs (p: Target.expr) (s: Target.expr) : Target.expr =
  FuncExp (Id "fs", [p; s])

(* Given a file permissions object, codegen setting the fs object's mode *)
let codegen_file_perms (fs: Target.expr) (p: Ast.file_perms)
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

(* Given a file description codegen setting the fs-object information *)
let codegen_file_info (fs: Target.expr) (owner : ParseTree.value option)
  (group : ParseTree.value option) perms env
  : (Target.stmt list * env, string) result =
  let res_mode = codegen_file_perms fs perms
  in let res_group =
    match group with
    | None -> Ok (res_mode, env)
    | Some (Str g) -> Ok (
          Assign (Field (fs, "owner_group"), StringLit g) :: res_mode,
          env)
    | Some (Unknown v) ->
        Result.bind (add_unknown env v Target.String) (fun map ->
          Ok (Target.Assign (Field (fs, "owner_group"), Id ("?" ^ v))
              :: res_mode, map))
  in Result.bind res_group (fun (res_group, map_group) ->
    match owner with
    | None -> Ok (res_group, map_group)
    | Some (Str u) -> Ok (
        Assign (Field (fs, "owner"), StringLit u) :: res_group,
        map_group)
    | Some (Unknown v) ->
        Result.bind (add_unknown map_group v Target.String) (fun map ->
          Ok (Target.Assign (Field (fs, "owner"), Id ("?" ^ v)) :: res_group,
              map)))

let codegen_file_desc (fs: Target.expr) (p: Ast.file_desc) env
  : (Target.stmt list * env, string) result =
  let { Ast.path = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms env

let codegen_files_desc (fs: Target.expr) (p: Ast.files_desc) env
  : (Target.stmt list * env, string) result =
  let { Ast.paths = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms env

let codegen_condition (c: Ast.cond) thn els env
  : (Target.stmt * env, string) result =
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
            env)
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
            env)
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
            env)
      | DebianFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "Debian",
              Eq),
            thn,
            els),
            env)
      | RedHatFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "RedHat",
              Eq),
            thn,
            els),
            env)
      end
  (* For file and directory exists we check the existance of the file-system
   * object and if it exists we assert it is a file/directory since normally
   * people don't check for the presence of a file/directory and expect to find
   * the other, they expect to either find what they expect or nothing *)
  | FileExists p ->
      Result.bind (codegen_path p env) (fun (map, path, system) ->
        Ok (
          Target.IfExists (
            fs path system,
            Assert (FuncExp (Id "is_file", [path; system])) :: thn,
            els),
          map))
  | DirExists p ->
      Result.bind (codegen_path p env) (fun (map, path, system) ->
        Ok (
          Target.IfExists (
            fs path system,
            Assert (FuncExp (Id "is_dir", [path; system])) :: thn,
            els),
          map))
  | PkgInstalled { name; pkg_manager } ->
      let check =
        match pkg_manager with
        (* We only care about the package manager if it specifies a virtual
         * environment since that changes how we check whether it is installed *)
        | System | Apt | Dnf | Pip None ->
            Ok ([Target.FuncExp (Id "e_package", [StringLit name])],
                env)
        | Pip (Some (Str path)) ->
            let virtenv
              = Target.FuncExp (Id "virtual_environment", [PathLit path])
            in Ok ([ virtenv;
                     FuncExp (Field (virtenv, "e_package"), [StringLit name]) ],
                     env)
        | Pip (Some (Unknown v)) ->
            let virtenv
              = Target.FuncExp (Id "virtual_environment", [Id v])
            in Result.bind (add_unknown env v Target.Path) (fun map ->
              Ok ([ virtenv;
                    FuncExp (Field (virtenv, "e_package"), [StringLit name]) ],
                    map))
      in Result.bind check (fun (conds, map) ->
        match conds with
        | [] -> failwith "Expected at least one condition to check if package is installed"
        | top :: rest ->
            Ok (Target.IfExists (top,
                List.fold_left
                  (fun thn cond -> [Target.IfExists (cond, thn, els)])
                  thn
                  rest,
                els), map))
  | ServiceRunning serv ->
      let service = Target.FuncExp (Id "e_service", [StringLit serv])
      in Ok (Target.IfExists (service,
              [IfThenElse (Field (service, "running"), thn, els)],
              els), env)

let codegen_act (a: Ast.act) env
  : (Target.stmt list * env, string) result =
  match a with
  | CloneGitRepo { repo; version; dest } ->
      Result.bind (codegen_path dest.path env)
        (fun (dst_map, dir_path, sys) ->
          let version =
            match version with
            | None -> Ok (Target.StringLit "HEAD", dst_map)
            | Some (Str s) -> Ok (Target.StringLit s, dst_map)
            | Some (Unknown v) -> 
                Result.bind (add_unknown dst_map v Target.String)
                  (fun map -> Ok (Target.Id ("?" ^ v), map))
          in Result.bind version (fun (version, v_map) ->
            let files = Target.FuncExp (Id "git_files",
              [StringLit repo; version; StringLit "origin"])
            in Result.bind (codegen_file_desc (fs dir_path sys) dest v_map)
              (fun (desc, map) ->
                Ok (Target.Assign (
                  Field (fs dir_path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "directory", [
                    ForEachExp ("f", files,
                      [ LetStmt ("p", FuncExp (Id "cons_path", [dir_path; Id "f"]))
                      ; Assign (
                          Field(fs (Id "p") sys, "fs_type"),
                          EnumExp (Id "file_type", None, "file", [
                            FuncExp (Id "git_content",
                              [StringLit repo; version; StringLit "origin"
                              ; Id "f"])
                          ])
                        )
                      ; Yield (Id "p")])
                    ])
                  ) :: desc, map))))
  | CopyDir { src; dest } ->
      Result.bind (codegen_path src env)
        (fun (src_map, src_path, src_sys) ->
        Result.bind (codegen_path dest.path src_map)
          (fun (dst_map, dst_path, dst_sys) ->
          Result.bind (codegen_file_desc (fs dst_path dst_sys) dest dst_map)
            (fun (desc, map) ->
              Ok (Target.AssertExists (fs src_path src_sys)
              :: Assert (FuncExp (Id "is_dir", [src_path; src_sys]))
              :: LetStmt ("files",
                  ForEachExp (
                    "file",
                    FuncExp (Id "get_dir_contents", [src_path; src_sys]),
                    [ AssertExists (fs (Id "file") src_sys)
                    ; Assert (FuncExp (Id "is_file", [Id "file"; src_sys]))
                    ; LetStmt ("res",
                        FuncExp (Id "cons_path", [dst_path;
                          FuncExp (Id "path_from", [src_path; Id "file"])]))
                    ; Assign (Field (fs (Id "res") dst_sys, "fs_type"),
                              Field (fs (Id "file") src_sys, "fs_type"))
                    ; Yield (Id "res") ]))
              :: Assign (Field (fs dst_path dst_sys, "fs_type"),
                         EnumExp (Id "file_type", None, "directory",
                                  [Id "files"]))
              :: desc, map))))
  | CopyFile { src; dest } ->
      Result.bind (codegen_path src env) 
        (fun (src_map, src_path, src_sys) ->
        Result.bind (codegen_path dest.path src_map)
          (fun (dst_map, dst_path, dst_sys) ->
            Result.bind (codegen_file_desc (fs dst_path dst_sys) dest dst_map)
              (fun (desc, map) ->
                Ok (Target.AssertExists (fs src_path src_sys)
                :: Assert (FuncExp (Id "is_file", [src_path; src_sys]))
                :: Assign (Field (fs dst_path dst_sys, "fs_type"),
                           Field (fs src_path src_sys, "fs_type"))
                :: desc, map))))
  | CopyFiles { src; dest } ->
      Result.bind (codegen_paths src env)
        (fun (src_map, src_paths, src_sys) ->
          match dest.paths with Glob _ -> Error "Cannot copy into a glob"
          | InPath dst -> Result.bind (codegen_path dst src_map)
            (fun (dst_map, dst_path, dst_sys) ->
              let dst_file =
                Target.FuncExp (Id "cons_path",
                  [ dst_path; FuncExp (Id "base_name", [Id "f"]) ])
              in Result.bind 
                (codegen_files_desc (fs dst_file dst_sys) dest dst_map)
                (fun (desc, map) ->
                  Ok (Target.ForLoop ("f", src_paths,
                      Assert (FuncExp (Id "is_file", [Id "f"; src_sys]))
                      :: Assign (Field (fs dst_file dst_sys, "fs_type"),
                          Field (fs (Id "f") src_sys, "fs_type"))
                      :: desc) :: [], map))))
  | CreateDir { dest } ->
      Result.bind (codegen_path dest.path env)
        (fun (path_map, path, sys) ->
          Result.bind (codegen_file_desc (fs path sys) dest path_map)
            (fun (desc, map) ->
              Ok (Target.Assign (
                    Field (fs path sys, "fs_type"),
                    EnumExp (Id "file_type", None, "directory",
                      [EnumExp (Id "list", Some Path, "nil", [])]))
               :: desc, map)))
  | CreateFile { dest; content } ->
      let content = Option.value ~default:"" content
      in Result.bind (codegen_path dest.path env)
        (fun (path_map, path, sys) ->
          Result.bind (codegen_file_desc (fs path sys) dest path_map)
            (fun (desc, map) ->
              Ok (Target.Assign (
                    Field (fs path sys, "fs_type"),
                    EnumExp (Id "file_type", None, "file",
                      [StringLit content]))
               :: desc, map)))
  | CreateGroup { name } ->
      Ok ([Target.Touch (FuncExp (Id "e_group", [StringLit name]))],
          env)
  (* NOTE: We should add options for key-type and probably other fields *)
  | CreateSshKey { loc } ->
      Result.bind (codegen_path loc env) (fun (map, path, sys) ->
        Ok (Target.LetStmt ("time", GenUnknown Int)
        :: Target.LetStmt ("comment", GenUnknown String)
        :: Assign (Field (fs path sys, "fs_type"),
            EnumExp (Id "file_type", None, "file",
              [ FuncExp (Id "ssh_private_key",
                [ StringLit "rsa"
                ; FuncExp (Id "default_ssh_key_bits", [])
                ; EnumExp (Id "option", Some String, "nothing", [])
                ; Id "comment"
                ; Id "time" ]) ]))
        :: Assign (
          Field (fs (FuncExp (Id "add_ext", [path; StringLit ".pub"])) sys, 
                "fs_type"),
            EnumExp (Id "file_type", None, "file",
              [ FuncExp (Id "ssh_public_key",
                [ StringLit "rsa"
                ; FuncExp (Id "default_ssh_key_bits", [])
                ; EnumExp (Id "option", Some String, "nothing", [])
                ; Id "comment"
                ; Id "time" ]) ]))
        :: [], map))
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
      let path =
        match loc with
        | Controller _ -> Error "Virtual Environment must be on remote machine"
        | Remote (Value v) ->
            codegen_value v Target.Path (fun s -> Target.PathLit s) env
        | Remote (InHome (user, v)) ->
            Result.bind
              (codegen_value v Target.Path (fun s -> Target.PathLit s) env)
              (fun (env, path) ->
                Ok (env, Target.FuncExp (Id "cons_path", [
                  Field (FuncExp (Id "e_user", [StringLit user]), "homedir");
                  path
                ])))
      in Result.bind path (fun (map, path) ->
        let virtenv = Target.FuncExp (Id "virtual_environment", [path])
        in let set_version =
          match version with
          | None -> []
          | Some s -> 
              Target.Assign (Field (virtenv, "python_version"),
                             StringLit ("python" ^ s))
              :: []
        in Ok (Target.Touch virtenv :: set_version, map))
  | DeleteDir { loc } ->
      Result.bind (codegen_path loc env)
        (fun (map, path, sys) -> Ok (
          Target.ForLoop ("f", FuncExp (Id "get_dir_contents", [path; sys]),
            [Clear (fs (Id "f") sys)])
          :: Clear (fs path sys) :: [], map))
  | DeleteFile { loc } ->
      Result.bind (codegen_path loc env)
        (fun (map, path, sys) -> Ok (
          Target.Assert (FuncExp (Id "is_file", [path; sys]))
          :: Target.Clear (fs path sys) :: [], map))
  | DeleteFiles { loc } ->
      Result.bind (codegen_paths loc env) (fun (map, paths, sys) ->
        Ok (Target.ForLoop ("f", paths,
            [ Assert (FuncExp (Id "is_file", [Id "f"; sys]))
            ; Clear (fs (Id "f") sys) ]) :: [], map))
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
              FuncExp (Id "regex_matches",
                [ StringLit ("^" ^ user ^ ".*NOPASSWD"); Id "c" ]),
              [ LetStmt ("r",
                  FuncExp (Id "replace_last", 
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
        :: LetStmt ("r", FuncExp (Id "remove_lines", 
            [ StringLit ("^" ^ user); Id "c" ]))
        :: Assert (FuncExp (Id "validate_contents",
            [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
        :: Assign (Field (fs path sys, "fs_type"),
            EnumExp (Id "file_type", None, "file", [ Id "r" ]))
        :: [], env)
  | DownloadFile { dest; src } ->
      Result.bind (codegen_path dest.path env)
        (fun (path_map, path, sys) ->
          Result.bind (codegen_file_desc (fs path sys) dest path_map)
            (fun (desc, map) ->
              Ok (Target.Assign (
                    Field (fs path sys, "fs_type"),
                    EnumExp (Id "file_type", None, "file",
                      [FuncExp (Id "download_url",
                        [PathLit src;
                          EnumExp (Id "option",
                            Some (Product [String; String]), "nothing", [])])]))
               :: desc, map)))
  | EnableSudo { who; passwordless } ->
      let user =
        match who with
        | User name -> name
        | Group name -> "%" ^ name
      in let line =
        let spec = "ALL=(ALL:ALL)"
        in let cmd = if passwordless then "NOPASSWD:ALL" else "ALL"
        in user ^ "\t" ^ spec ^ " " ^ cmd
      in let path = Target.PathLit "/etc/sudoers"
      in let sys = Target.EnumExp (Id "file_system", None, "remote", [])
      in Ok (Target.LetStmt ("c", FuncExp (Id "get_file_content", [path; sys]))
         :: Target.IfThenElse (
              (* FIXME: in regex_matches and replace_last we should use a form
               * of user that is a regex. As long as the name doesn't contain
               * special regex characters, this is fine and so probably is
               * alright for the moment *)
              FuncExp (Id "regex_matches", [ StringLit ("^" ^ user); Id "c" ]),
              [ LetStmt ("r",
                  FuncExp (Id "replace_last", 
                    [ StringLit ("^" ^ user) ; StringLit line ; Id "c" ]))
              ; Assert (FuncExp (Id "validate_contents",
                  [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
              ; Assign (Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file", [Id "r"]))
              ],
              [ LetStmt ("r",
                  BinaryExp (Id "c", StringLit (line ^ "\\n"), Concat))
              ; Assert (FuncExp (Id "validate_contents",
                  [ StringLit "/usr/sbin/visudo -cf %s"; Id "r" ]))
              ; Assign (Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file", [Id "r"]))
              ])
         :: [], env)
  | InstallPkg { pkg = { name; pkg_manager }; version } ->
      let pkg_info =
        match pkg_manager with
        | Apt ->
            let pkg = Target.FuncExp (Id "e_package", [StringLit name])
            in Ok (env,
                   [Target.Touch (FuncExp (Field (pkg, "e_apt"), []))],
                   pkg)
        | Dnf ->
            let pkg = Target.FuncExp (Id "e_package", [StringLit name])
            in Ok (env,
                   [Target.Touch (FuncExp (Field (pkg, "e_dnf"), []))],
                   pkg)
        | Pip None ->
            let pkg = Target.FuncExp (Id "e_package", [StringLit name])
            in Ok (env,
                   [Target.Touch (FuncExp (Field (pkg, "e_pip"), []))],
                   pkg)
        | System ->
            let pkg = Target.FuncExp (Id "e_package", [StringLit name])
            in Ok (env,
                   [Target.IfThenElse (
                      BinaryExp (
                        Field (FuncExp (Id "env", []), "os_family"),
                        StringLit "Debian",
                        Eq),
                      [ Touch (FuncExp (Field (pkg, "e_apt"), [])) ],
                      [ Target.IfThenElse (
                        BinaryExp (
                          Field (FuncExp (Id "env", []), "os_family"),
                          StringLit "RedHat",
                          Eq),
                        [ Touch (FuncExp (Field (pkg, "e_dnf"), [])) ],
                        [ Touch (FuncExp (Field (pkg, "sys"), [])) ])
                   ])],
                   pkg)
        | Pip (Some p) ->
            let path =
              match p with Str s -> Ok (env, Target.PathLit s)
              | Unknown v -> Result.bind (add_unknown env v Target.Path)
                                         (fun map -> Ok (map, Target.Id v))
            in Result.bind path (fun (map, path) ->
              let virtenv =
                Target.FuncExp (Id "virtual_environment", [path])
              in let pkg =
                Target.FuncExp (Field (virtenv, "e_package"), [StringLit name])
              in Ok (map,
                     [ Target.AssertExists virtenv
                     ; Touch (FuncExp (Field (pkg, "e_pip"), [])) ],
                     pkg))
      in Result.bind pkg_info (fun (map, setup, pkg) ->
        match version with
        | None -> Ok (setup, map)
        | Some "latest" -> Ok (setup
          @ [Target.Assign (
              Field (pkg, "version"), 
              EnumExp (Id "package_version", None, "latest", []))], map)
        | Some v -> Ok (setup
          @ [Target.Assign (
              Field (pkg, "version"),
              EnumExp (Id "package_version", None, "specific", [StringLit v]))]
          , map))
  | MoveDir { src; dest } ->
      Result.bind (codegen_path src env)
        (fun (src_map, src_path, src_sys) ->
        Result.bind (codegen_path dest.path src_map)
          (fun (dst_map, dst_path, dst_sys) ->
          Result.bind (codegen_file_desc (fs dst_path dst_sys) dest dst_map)
            (fun (desc, map) ->
              Ok (Target.AssertExists (fs src_path src_sys)
              :: Assert (FuncExp (Id "is_dir", [src_path; src_sys]))
              :: LetStmt ("files",
                  ForEachExp (
                    "file",
                    FuncExp (Id "get_dir_contents", [src_path; src_sys]),
                    [ AssertExists (fs (Id "file") src_sys)
                    ; Assert (FuncExp (Id "is_file", [Id "file"; src_sys]))
                    ; LetStmt ("res",
                        FuncExp (Id "cons_path", [dst_path;
                          FuncExp (Id "path_from", [src_path; Id "file"])]))
                    ; Assign (Field (fs (Id "res") dst_sys, "fs_type"),
                              Field (fs (Id "file") src_sys, "fs_type"))
                    ; Clear (fs (Id "file") src_sys)
                    ; Yield (Id "res") ]))
              :: Assign (Field (fs dst_path dst_sys, "fs_type"),
                         EnumExp (Id "file_type", None, "directory",
                                  [Id "files"]))
              :: Clear (fs src_path src_sys)
              :: desc, map))))
  | MoveFile { src; dest } ->
      Result.bind (codegen_path src env)
        (fun (src_map, src_path, src_sys) ->
        Result.bind (codegen_path dest.path src_map)
          (fun (dst_map, dst_path, dst_sys) ->
            Result.bind (codegen_file_desc (fs dst_path dst_sys) dest dst_map)
              (fun (desc, map) ->
                Ok (Target.AssertExists (fs src_path src_sys)
                 :: Assert (FuncExp (Id "is_file", [src_path; src_sys]))
                 :: Assign (Field (fs dst_path dst_sys, "fs_type"),
                            Field (fs src_path src_sys, "fs_type"))
                 :: Clear (fs src_path src_sys)
                 :: desc, map))))
  | MoveFiles { src; dest } ->
      Result.bind (codegen_paths src env)
        (fun (src_map, src_paths, src_sys) ->
          match dest.paths with Glob _ -> Error "Cannot move into a glob"
          | InPath dst -> Result.bind (codegen_path dst src_map)
            (fun (dst_map, dst_path, dst_sys) ->
              let dst_file =
                Target.FuncExp (Id "cons_path",
                  [ dst_path; FuncExp (Id "base_name", [Id "f"]) ])
              in Result.bind 
                (codegen_files_desc (fs dst_file dst_sys) dest dst_map)
                (fun (desc, map) ->
                  Ok (Target.ForLoop ("f", src_paths,
                      Assert (FuncExp (Id "is_file", [Id "f"; src_sys]))
                      :: Assign (Field (fs dst_file dst_sys, "fs_type"),
                          Field (fs (Id "f") src_sys, "fs_type"))
                      :: Clear (fs (Id "f") src_sys)
                      :: desc) :: [], map))))
  | Reboot -> Ok (
    Target.LetStmt ("time", GenUnknown Int)
    :: Assert (BinaryExp (IntLit 0, Id "time", Le))
    :: Assign (Field (FuncExp (Id "env", []), "last_reboot"), Id "time")
    :: [], env)
  (* FIXME: Like with the sudoers file, I think it would be better to assert
   * about the result *)
  | SetEnvVar { name; value } ->
      let value =
        match value with
        | Str s -> Ok (env, Target.StringLit s)
        | Unknown v -> Result.bind (add_unknown env v Target.String)
            (fun map -> Ok (map, Target.Id ("?" ^ v)))
      in Result.bind value (fun (map, value) ->
        let path = Target.PathLit "/etc/environment"
        in let sys = Target.EnumExp (Id "file_system", None, "remote", [])
        in let regex = Target.StringLit ("^" ^ name ^ "=")
        in let line =
          Target.BinaryExp (StringLit (name ^ "="), value, Concat)
        in Ok (
          Target.LetStmt ("c", FuncExp (Id "get_file_content", [path; sys]))
          :: Target.IfThenElse (
            FuncExp (Id "regex_matches", [ regex; Id "c" ]),
            [ LetStmt ("r",
                FuncExp (Id "replace_last",
                  [ regex; line; Id "c" ]))
            ; Assign (Field (fs path sys, "fs_type"),
                EnumExp (Id "file_type", None, "file", [Id "r"]))
            ],
            [ LetStmt ("r", BinaryExp (Id "c", 
                BinaryExp (line, StringLit "\\n", Concat), Concat))
            ; Assign (Field (fs path sys, "fs_type"),
                EnumExp (Id "file_type", None, "file", [Id "r"]))
            ])
          :: [], map))
  | SetFilePerms { loc; perms } ->
      Result.bind (codegen_path loc env) (fun (map, path, sys) ->
        Ok (Target.Assert (FuncExp (Id "is_file", [path; sys]))
        :: codegen_file_perms (fs path sys) perms, map))
  | SetFilesPerms { locs; perms } ->
      Result.bind (codegen_paths locs env) (fun (map, paths, sys) ->
        Ok (Target.ForLoop ("f", paths,
          Assert (FuncExp (Id "is_file", [Id "f"; sys]))
          :: codegen_file_perms (fs (Id "f") sys) perms)
        :: [], map))
  | SetShell { user; shell } ->
      let shell =
        match shell with
        | Controller _ -> Error "Path to a user's shell must be a remote path"
        | Remote (Value v) ->
            codegen_value v Target.Path (fun s -> Target.PathLit s) env
        | Remote (InHome (user, v)) ->
            Result.bind
              (codegen_value v Target.Path (fun s -> Target.PathLit s) env)
              (fun (env, path) ->
                Ok (env, Target.FuncExp (Id "cons_path", [
                  Field (FuncExp (Id "e_user", [StringLit user]), "homedir");
                  path
                ])))
      in let user = Target.FuncExp (Id "e_user", [StringLit user])
      in Result.bind shell (fun (map, path) -> Ok (
        Target.AssertExists user
        :: Assign (Field (user, "default_shell"), path)
        :: [], map))
  | StartService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "e_service", [StringLit name]), "running"),
          BoolLit true) :: [], env)
  | StopService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "e_service", [StringLit name]), "running"),
          BoolLit false) :: [], env)
  | UninstallPkg { pkg = { name; pkg_manager } } ->
      begin match pkg_manager with
      | Apt | Dnf | Pip None | System ->
          Ok (Target.Clear (FuncExp (Id "e_package", [StringLit name])) :: [],
              env)
      | Pip (Some p) ->
          let path =
            match p with Str s -> Ok (env, Target.PathLit s)
            | Unknown v -> Result.bind (add_unknown env v Target.Path)
                                       (fun map -> Ok (map, Target.Id v))
          in Result.bind path (fun (map, path) ->
              let virtenv =
                Target.FuncExp (Id "virtual_environment", [path])
              in let pkg =
                Target.FuncExp (Field (virtenv, "e_package"), [StringLit name])
              in Ok (Target.AssertExists virtenv :: Clear pkg :: [], map))
      end
  | WriteFile { str; dest; position } ->
      Result.bind (codegen_path dest.path env)
      (fun (path_map, path, sys) ->
        Result.bind (codegen_file_desc (fs path sys) dest path_map)
        (fun (desc, desc_map) ->
          let str =
            match str with
            | Str s -> Ok (desc_map, Target.StringLit (s ^ "\\n"))
            | Unknown v -> Result.bind (add_unknown desc_map v Target.String)
                (fun map -> Ok (map, 
                  Target.BinaryExp (Id ("?" ^ v), StringLit "\\n", Concat)))
          in Result.bind str (fun (map, str) ->
            match position with
            | Overwrite -> Ok (
              Target.Assign (Field (fs path sys, "fs_type"),
                EnumExp (Id "file_type", None, "file", [str]))
              :: desc, map)
            | Top -> Ok (
              Target.LetStmt ("c",
                FuncExp (Id "get_file_content", [path; sys]))
              :: Target.Assign (Field (fs path sys, "fs_type"),
                EnumExp (Id "file_type", None, "file",
                  [BinaryExp (str, Id "c", Concat)]))
              :: desc, map)
            | Bottom -> Ok (
              Target.LetStmt ("c",
                FuncExp (Id "get_file_content", [path; sys]))
              :: Target.Assign (Field (fs path sys, "fs_type"),
                EnumExp (Id "file_type", None, "file",
                  [BinaryExp (Id "c", str, Concat)]))
              :: desc, map))))

let codegen_query (q: Ast.query)
  : (Target.stmt list, string) result =
  let rec codegen (q: Ast.query) env =
    match q with
    | End -> Ok ([], env)
    | Atom act -> codegen_act act env
    | Seq (fst, snd) ->
        Result.bind (codegen fst env) (fun (fst, fst_map) ->
          Result.bind (codegen snd fst_map) (fun (snd, res_map) ->
            Ok (fst @ snd, res_map)))
    | Cond (c, thn, els) ->
        Result.bind (codegen thn env) (fun (thn, thn_map) ->
          Result.bind (codegen els thn_map) (fun (els, els_map) ->
            Result.bind (codegen_condition c thn els els_map) 
              (fun (res, res_map) ->
                Ok ([res], res_map))))
  in Result.bind (codegen q env_empty) (fun (code, env) ->
    let setup =
      Target.AssertExists (FuncExp (Id "env", []))
      :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"), IntLit 0, Eq))
      :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "last_reboot"), IntLit (-1), Eq))
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
        Target.LetStmt ("?" ^ v, GenUnknown t) :: c
      ) env.unknowns assert_users
    in Ok bind_unknowns)
