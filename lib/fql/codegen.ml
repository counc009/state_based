module Target = Modules.Ast

module StringMap = Map.Make(String)
type typ = Target.typ

let join_maps x y =
  let err = ref None
  in let res =
    StringMap.merge
      (fun v x y ->
        match x, y with
        | None, None -> None
        | Some t, None | None, Some t -> Some t
        | Some x, Some y when x = y -> Some x
        | _, _ -> err := Some v; None)
      x y
  in match !err with
  | None -> Ok res
  | Some v -> Error (Printf.sprintf 
                      "Unknown '%s' required to have different types" v)

(* Returns the unknown map and then the path and system as expressions *)
let codegen_path (p: Ast.path) : typ StringMap.t * Target.expr * Target.expr =
  let (map, path, sys) =
    match p with
    | Controller (Str s) -> (StringMap.empty, Target.PathLit s, "local")
    | Controller (Unknown v) ->
        (StringMap.singleton v Target.Path, Id ("?" ^ v), "local")
    | Remote (Str s) -> (StringMap.empty, Target.PathLit s, "remote")
    | Remote (Unknown v) ->
        (StringMap.singleton v Target.Path, Id ("?" ^ v), "remote")
  in let system = Target.EnumExp (Id "file_system", None, sys, [])
  in (map, path, system)

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
let codegen_file_desc (fs: Target.expr) (p: Ast.file_desc)
  : (Target.stmt list * typ StringMap.t, string) result =
  let { Ast.path= _; owner; group; perms } = p
  in let res_mode = codegen_file_perms fs perms
  in let (res_group, map_group) =
    match group with
    | None -> (res_mode, StringMap.empty)
    | Some (Str g) ->
        (Assign (Field (fs, "owner_group"), StringLit g) :: res_mode,
         StringMap.empty)
    | Some (Unknown v) ->
        (Assign (Field (fs, "owner_group"), Id ("?" ^ v)) :: res_mode,
         StringMap.singleton v Target.String)
  in match owner with
    | None -> Ok (res_group, map_group)
    | Some (Str u) -> Ok (
        Assign (Field (fs, "owner"), StringLit u) :: res_group,
        map_group)
    | Some (Unknown v) ->
        Result.bind (join_maps map_group (StringMap.singleton v Target.String))
          (fun map ->
            Ok (Target.Assign (Field (fs, "owner"), Id ("?" ^ v)) :: res_group,
                map))

let codegen_condition (c: Ast.cond) thn els : (Target.stmt * typ StringMap.t, string) result =
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
            StringMap.empty)
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
            StringMap.empty)
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
            StringMap.empty)
      | DebianFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "Debian",
              Eq),
            thn,
            els),
            StringMap.empty)
      | RedHatFamily -> Ok (
          IfThenElse (
            BinaryExp (
              Field (FuncExp (Id "env", []), "os_family"),
              StringLit "RedHat",
              Eq),
            thn,
            els),
            StringMap.empty)
      end
  (* For file and directory exists we check the existance of the file-system
   * object and if it exists we assert it is a file/directory since normally
   * people don't check for the presence of a file/directory and expect to find
   * the other, they expect to either find what they expect or nothing *)
  | FileExists p ->
      let (map, path, system) = codegen_path p
      in Ok (
        IfExists (
          fs path system,
          Assert (FuncExp (Id "is_file", [path; system])) :: thn,
          els),
        map)
  | DirExists p ->
      let (map, path, system) = codegen_path p
      in Ok (
        IfExists (
          fs path system,
          Assert (FuncExp (Id "is_dir", [path; system])) :: thn,
          els),
        map)
  | PkgInstalled _pkg -> Error "Checking PkgInstalled not implemented"
  | ServiceRunning _serv -> Error "Checking ServiceRunning not implemented"

let codegen_act (a: Ast.act)
  : (Target.stmt list * typ StringMap.t, string) result =
  match a with
  | CloneGitRepo _ -> Error "TODO: Handle CloneGitRepo"
  | CopyDir _ -> Error "TODO: Handle CopyDir"
  | CopyFile { src; dest } ->
      let (src_map, src_path, src_sys) = codegen_path src
      in let (dst_map, dst_path, dst_sys) = codegen_path dest.path
      in Result.bind (join_maps src_map dst_map) (fun paths_map ->
        Result.bind (codegen_file_desc (fs dst_path dst_sys) dest)
        (fun (desc, desc_map) ->
          Result.bind (join_maps paths_map desc_map) (fun map ->
           Ok (Target.AssertExists (fs src_path src_sys)
            :: Assert (FuncExp (Id "is_file", [src_path; src_sys]))
            :: Assign (Field (fs dst_path dst_sys, "fs_type"),
                       Field (fs src_path src_sys, "fs_type"))
            :: desc, map))))
  | CopyFiles _ -> Error "TODO: Handle CopyFiles"
  | CreateDir { dest } ->
      let (path_map, path, sys) = codegen_path dest.path
      in Result.bind (codegen_file_desc (fs path sys) dest)
        (fun (desc, desc_map) ->
          Result.bind (join_maps path_map desc_map) (fun map ->
            Ok (Target.Assign (
                  Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "directory",
                    [EnumExp (Id "list", Some Path, "nil", [])]))
             :: desc, map)))
  | CreateFile { dest; content } ->
      let content = Option.value ~default:"" content
      in let (path_map, path, sys) = codegen_path dest.path
      in Result.bind (codegen_file_desc (fs path sys) dest)
        (fun (desc, desc_map) ->
          Result.bind (join_maps path_map desc_map) (fun map ->
            Ok (Target.Assign (
                  Field (fs path sys, "fs_type"),
                  EnumExp (Id "file_type", None, "file",
                    [StringLit content]))
             :: desc, map)))
  | CreateGroup { name } ->
      Ok ([Target.Touch (FuncExp (Id "group", [StringLit name]))],
          StringMap.empty)
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
      in Ok (Target.Touch user :: res_group, StringMap.empty)
  | CreateVirtualEnv _ -> Error "TODO: Handle CreateVirtualEnv"
  | DeleteDir _ -> Error "TODO: Handle DeleteDir"
  | DeleteFile { loc } ->
      let (map, path, sys) = codegen_path loc
      in Ok (Target.Clear (fs path sys) :: [], map)
  | DeleteFiles _ -> Error "TODO: Handle DeleteFiles"
  | DeleteGroup { name } -> Ok (
      Target.Clear (FuncExp (Id "group", [StringLit name])) :: [],
      StringMap.empty)
  | DeleteUser { name } -> Ok (
      Target.Clear (FuncExp (Id "user", [StringLit name])) :: [],
      StringMap.empty)
  | DisablePassword { user } -> Ok (
      Target.Assign (Field (FuncExp (Id "user", [StringLit user]), "password"),
                     EnumExp (Id "password_set", None, "disabled", []))
      :: [], StringMap.empty)
  | DisableSudo _ -> Error "TODO: Handle DisableSudo"
  | DownloadFile { dest; src } ->
      let (path_map, path, sys) = codegen_path dest.path
      in Result.bind (codegen_file_desc (fs path sys) dest)
        (fun (desc, desc_map) ->
          Result.bind (join_maps path_map desc_map) (fun map ->
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
      let (src_map, src_path, src_sys) = codegen_path src
      in let (dst_map, dst_path, dst_sys) = codegen_path dest.path
      in Result.bind (join_maps src_map dst_map) (fun paths_map ->
        Result.bind (codegen_file_desc (fs dst_path dst_sys) dest)
        (fun (desc, desc_map) ->
          Result.bind (join_maps paths_map desc_map) (fun map ->
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
      let (map, path, sys) = codegen_path loc
      in Ok (codegen_file_perms (fs path sys) perms, map)
  | SetFilesPerms _ -> Error "TODO: Handle SetFilesPerms"
  | SetShell { user; shell } ->
      let shell =
        match shell with
        | Controller _ -> Error "Path to a user's shell must be a remote path"
        | Remote (Str s) -> Ok (StringMap.empty, Target.PathLit s)
        | Remote (Unknown v) ->
            Ok (StringMap.singleton v Target.Path, Target.Id ("?" ^ v))
      in let user = Target.FuncExp (Id "user", [StringLit user])
      in Result.bind shell (fun (map, path) -> Ok (
        Target.AssertExists user
        :: Assign (Field (user, "default_shell"), path)
        :: [], map))
  | StartService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "service", [StringLit name]), "running"),
          BoolLit true) :: [], StringMap.empty)
  | StopService { name } ->
      Ok (Target.Assign (
          Field (FuncExp (Id "service", [StringLit name]), "running"),
          BoolLit false) :: [], StringMap.empty)
  | UninstallPkg _ -> Error "TODO: Handle UninstallPkg"
  | WriteFile _ -> Error "TODO: Handle WriteFile"

let codegen_query (q: Ast.query)
  : (Target.stmt list, string) result =
  let rec codegen (q: Ast.query) =
    match q with
    | End -> Ok ([], StringMap.empty)
    | Atom act -> codegen_act act
    | Seq (fst, snd) ->
        Result.bind (codegen fst) (fun (fst, fst_map) ->
          Result.bind (codegen snd) (fun (snd, snd_map) ->
            Result.bind (join_maps fst_map snd_map) (fun map ->
              Ok (fst @ snd, map))))
    | Cond (c, thn, els) ->
        Result.bind (codegen thn) (fun (thn, thn_map) ->
          Result.bind (codegen els) (fun (els, els_map) ->
            Result.bind (codegen_condition c thn els) (fun (res, res_map) ->
              Result.bind (join_maps thn_map els_map) (fun branch_map ->
                Result.bind (join_maps branch_map res_map) (fun map ->
                  Ok ([res], map))))))
  in Result.bind (codegen q) (fun (code, unknowns) ->
    let setup =
      Target.AssertExists (FuncExp (Id "env", []))
      :: Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"), IntLit 0, Eq))
      :: code
    in Ok (StringMap.fold (fun v t c ->
                          Target.LetStmt ("?" ^ v, GenUnknown t) :: c)
                       unknowns setup))
