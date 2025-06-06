module Target = Modules.Ast

module StringMap = Map.Make(String)
type typ = Target.typ

let add_unknown (unknowns : typ StringMap.t) (nm: string) (ty: typ)
  : (typ StringMap.t, string) result =
  let err = ref false
  in let map = StringMap.update nm (fun t ->
    match t with
    | None -> Some ty
    | Some t when t = ty -> Some ty
    | Some _ -> err := true; t) unknowns
  in if !err
  then Error (Printf.sprintf "Unknown '%s' used with different types" nm)
  else Ok map

(* Returns the unknown map and then the path and system as expressions *)
let codegen_path (p: Ast.path) unknowns
  : (typ StringMap.t * Target.expr * Target.expr, string) result =
  let sys =
    match p with Controller _ -> "local" | Remote _ -> "remote"
  in let path =
    match p with
    | Controller (Str s) | Remote (Str s) -> Ok (unknowns, Target.PathLit s)
    | Controller (Unknown v) | Remote (Unknown v) ->
        Result.bind (add_unknown unknowns v Target.Path)
          (fun map -> Ok (map, Target.Id ("?" ^ v)))
  in let system = Target.EnumExp (Id "file_system", None, sys, [])
  in Result.bind path (fun (map, path) -> Ok (map, path, system))

let codegen_paths (p: Ast.paths) unknowns =
  match p with
  | InPath p ->
      Result.bind (codegen_path p unknowns) (fun (map, p, sys) ->
        Ok (map, Target.FuncExp (Id "get_dir_contents", [p; sys]), sys))
  | Glob { base; glob } ->
      (* TODO: Really should change how globs work so that it works more
       * like the no glob case, but that'll require fixing other stuff *)
      let s = match base with | Controller _ -> "local" | Remote _ -> "remote"
      in let sys = Target.EnumExp (Id "file_system", None, s, [])
      in let path =
        match base with
        | Controller (Str s) | Remote (Str s)
            -> Ok (Target.PathLit s, unknowns)
        | Controller (Unknown v) | Remote (Unknown v)
            -> Result.bind (add_unknown unknowns v Target.Path)
                (fun map -> Ok (Target.Id ("?" ^ v), map))
      in Result.bind path (fun (path, map) ->
        let glob_expr =
          Target.FuncExp (Id "string_of_path",
            [ FuncExp (Id "cons_path", [ path; PathLit glob ]) ])
        in let globs = Target.EnumExp (Id "list", Some String, "cons",
                      [ glob_expr
                      ; EnumExp (Id "list", Some String, "nil", [])])
        in let paths = Target.FuncExp (Id "file_glob",
          [globs; EnumExp (Id "find_file_type", None, "file", [])
          ; sys])
        in Ok (map, paths, sys))

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
      in if perm = "" then None else Some ("o=" ^ perm)
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
  (group : ParseTree.value option) perms unknowns
  : (Target.stmt list * typ StringMap.t, string) result =
  let res_mode = codegen_file_perms fs perms
  in let res_group =
    match group with
    | None -> Ok (res_mode, unknowns)
    | Some (Str g) -> Ok (
          Assign (Field (fs, "owner_group"), StringLit g) :: res_mode,
          unknowns)
    | Some (Unknown v) ->
        Result.bind (add_unknown unknowns v Target.String) (fun map ->
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

let codegen_file_desc (fs: Target.expr) (p: Ast.file_desc) unknowns
  : (Target.stmt list * typ StringMap.t, string) result =
  let { Ast.path = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms unknowns

let codegen_files_desc (fs: Target.expr) (p: Ast.files_desc) unknowns
  : (Target.stmt list * typ StringMap.t, string) result =
  let { Ast.paths = _; owner; group; perms } = p
  in codegen_file_info fs owner group perms unknowns

let codegen_condition (c: Ast.cond) thn els unknowns
  : (Target.stmt * typ StringMap.t, string) result =
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
            unknowns)
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
            unknowns)
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
            unknowns)
      | DebianFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "Debian",
              Eq),
            thn,
            els),
            unknowns)
      | RedHatFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "RedHat",
              Eq),
            thn,
            els),
            unknowns)
      end
  (* For file and directory exists we check the existance of the file-system
   * object and if it exists we assert it is a file/directory since normally
   * people don't check for the presence of a file/directory and expect to find
   * the other, they expect to either find what they expect or nothing *)
  | FileExists p ->
      Result.bind (codegen_path p unknowns) (fun (map, path, system) ->
        Ok (
          Target.IfExists (
            fs path system,
            Assert (FuncExp (Id "is_file", [path; system])) :: thn,
            els),
          map))
  | DirExists p ->
      Result.bind (codegen_path p unknowns) (fun (map, path, system) ->
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
            Ok ([Target.FuncExp (Id "package", [StringLit name])],
                unknowns)
        | Pip (Some (Str path)) ->
            let virtenv
              = Target.FuncExp (Id "virtual_environment", [PathLit path])
            in Ok ([ virtenv;
                     FuncExp (Field (virtenv, "package"), [StringLit name]) ],
                     unknowns)
        | Pip (Some (Unknown v)) ->
            let virtenv
              = Target.FuncExp (Id "virtual_environment", [Id v])
            in Result.bind (add_unknown unknowns v Target.Path) (fun map ->
              Ok ([ virtenv;
                    FuncExp (Field (virtenv, "package"), [StringLit name]) ],
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
      let service = Target.FuncExp (Id "service", [StringLit serv])
      in Ok (Target.IfExists (service,
              [IfThenElse (Field (service, "running"), thn, els)],
              els), unknowns)

let codegen_act (a: Ast.act) unknowns
  : (Target.stmt list * typ StringMap.t, string) result =
  match a with
  | CloneGitRepo { repo; version; dest } ->
      Result.bind (codegen_path dest.path unknowns)
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
      Result.bind (codegen_path src unknowns)
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
      Result.bind (codegen_path src unknowns) 
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
      Result.bind (codegen_paths src unknowns)
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
      Result.bind (codegen_path dest.path unknowns)
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
      in Result.bind (codegen_path dest.path unknowns)
        (fun (path_map, path, sys) ->
          Result.bind (codegen_file_desc (fs path sys) dest path_map)
            (fun (desc, map) ->
              Ok (Target.Assign (
                    Field (fs path sys, "fs_type"),
                    EnumExp (Id "file_type", None, "file",
                      [StringLit content]))
               :: desc, map)))
  | CreateGroup { name } ->
      Ok ([Target.Touch (FuncExp (Id "group", [StringLit name]))],
          unknowns)
  | CreateSshKey _ -> Error "TODO: Handle CreateSshKey"
  | CreateUser { name; group; groups } ->
      let user = Target.FuncExp (Id "user", [StringLit name])
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
            Target.Assign (Target.Field (user, "group"), StringLit group)
            :: res_groups
      in Ok (Target.Touch user :: res_group, unknowns)
  | CreateVirtualEnv _ -> Error "TODO: Handle CreateVirtualEnv"
  | DeleteDir _ -> Error "TODO: Handle DeleteDir"
  | DeleteFile { loc } ->
      Result.bind (codegen_path loc unknowns)
        (fun (map, path, sys) -> Ok (Target.Clear (fs path sys) :: [], map))
  | DeleteFiles _ -> Error "TODO: Handle DeleteFiles"
  | DeleteGroup { name } -> Ok (
      Target.Clear (FuncExp (Id "group", [StringLit name])) :: [],
      unknowns)
  | DeleteUser { name } -> Ok (
      Target.Clear (FuncExp (Id "user", [StringLit name])) :: [],
      unknowns)
  | DisablePassword { user } -> Ok (
      Target.Assign (Field (FuncExp (Id "user", [StringLit user]), "password"),
                     EnumExp (Id "password_set", None, "disabled", []))
      :: [], unknowns)
  | DisableSudo _ -> Error "TODO: Handle DisableSudo"
  | DownloadFile { dest; src } ->
      Result.bind (codegen_path dest.path unknowns)
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
  | EnableSudo _ -> Error "TODO: Handle EnableSudo"
  | InstallPkg _ -> Error "TODO: Handle InstallPkg"
  | MoveDir _ -> Error "TODO: Handle MoveDir"
  | MoveFile { src; dest } ->
      Result.bind (codegen_path src unknowns)
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
  | MoveFiles _ -> Error "TODO: Handle MoveFiles"
  | Reboot -> Error "TODO: Handle Reboot"
  | SetEnvVar _ -> Error "TODO: Handle SetenvVar"
  | SetFilePerms { loc; perms } ->
      Result.bind (codegen_path loc unknowns) (fun (map, path, sys) ->
        Ok (codegen_file_perms (fs path sys) perms, map))
  | SetFilesPerms _ -> Error "TODO: Handle SetFilesPerms"
  | SetShell { user; shell } ->
      let shell =
        match shell with
        | Controller _ -> Error "Path to a user's shell must be a remote path"
        | Remote (Str s) -> Ok (unknowns, Target.PathLit s)
        | Remote (Unknown v) ->
            Result.bind (add_unknown unknowns v Target.Path) (fun map ->
              Ok (map, Target.Id ("?" ^ v)))
      in let user = Target.FuncExp (Id "user", [StringLit user])
      in Result.bind shell (fun (map, path) -> Ok (
        Target.AssertExists user
        :: Assign (Field (user, "default_shell"), path)
        :: [], map))
  | StartService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "service", [StringLit name]), "running"),
          BoolLit true) :: [], unknowns)
  | StopService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "service", [StringLit name]), "running"),
          BoolLit false) :: [], unknowns)
  | UninstallPkg _ -> Error "TODO: Handle UninstallPkg"
  | WriteFile _ -> Error "TODO: Handle WriteFile"

let codegen_query (q: Ast.query)
  : (Target.stmt list, string) result =
  let rec codegen (q: Ast.query) unknowns =
    match q with
    | End -> Ok ([], unknowns)
    | Atom act -> codegen_act act unknowns
    | Seq (fst, snd) ->
        Result.bind (codegen fst unknowns) (fun (fst, fst_map) ->
          Result.bind (codegen snd fst_map) (fun (snd, res_map) ->
            Ok (fst @ snd, res_map)))
    | Cond (c, thn, els) ->
        Result.bind (codegen thn unknowns) (fun (thn, thn_map) ->
          Result.bind (codegen els thn_map) (fun (els, els_map) ->
            Result.bind (codegen_condition c thn els els_map) 
              (fun (res, res_map) ->
                Ok ([res], res_map))))
  in Result.bind (codegen q StringMap.empty) (fun (code, unknowns) ->
    let setup =
      Target.AssertExists (FuncExp (Id "env", []))
      :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"), IntLit 0, Eq))
      :: code
    in Ok (StringMap.fold (fun v t c ->
                          Target.LetStmt ("?" ^ v, GenUnknown t) :: c)
                       unknowns setup))
