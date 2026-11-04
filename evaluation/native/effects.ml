(* Inspectable effect trees from the actual upstream semantic AST.
   This representation is not a semantic-equivalence decision procedure. *)
open Fql.Ast
module M = Modules.Ast
module S = Fql.Semant.Semant(Fql.Knowledge.Example)
let str s =
  let b=Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c -> match c with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b
let obj xs = "{" ^ String.concat "," (List.map (fun (k,v)->str k ^ ":" ^ v) xs) ^ "}"
let arr xs = "[" ^ String.concat "," xs ^ "]"
let bool b = if b then "true" else "false"
let opt f = function None -> "null" | Some x -> f x
let tag name fields = obj (("kind",str name)::fields)
let unknowns = Hashtbl.create 8
let parsed = function
  | Fql.ParseTree.Str s -> str s
  | Unknown s ->
      let n=match Hashtbl.find_opt unknowns s with Some n->n | None ->
        let n=Hashtbl.length unknowns in Hashtbl.add unknowns s n; n in
      obj ["unknown",string_of_int n]
let rec typ = function
  | M.Bool -> str "bool" | Int -> str "int" | Float -> str "float"
  | String -> str "string" | Path -> str "path" | Unit -> str "unit"
  | Named s -> tag "named" ["name",str s]
  | Product xs -> tag "product" ["types",arr (List.map typ xs)]
  | List x -> tag "list" ["type",typ x] | Option x -> tag "option" ["type",typ x]
let binary = function
  | M.Or -> "or" | And -> "and" | Eq -> "eq" | Ne -> "ne" | Lt -> "lt"
  | Le -> "le" | Gt -> "gt" | Ge -> "ge" | LShift -> "lshift" | RShift -> "rshift"
  | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div" | Mod -> "mod"
  | Concat -> "concat" | Append -> "append"
let rec expr depth = function
  | M.Id s -> tag "id" ["name",str s]
  | BoolLit b -> tag "bool" ["value",bool b]
  | IntLit n -> tag "int" ["value",string_of_int n]
  | FloatLit n -> tag "float" ["value",str (string_of_float n)]
  | StringLit s -> tag "string" ["value",str s]
  | PathLit s -> tag "path" ["value",str s]
  | UnitExp -> tag "unit" []
  | GenUniversal t -> tag "universal" ["type",typ t]
  | GenExistential (t,predicate) ->
      let binder="__kb_bound_" ^ string_of_int depth in
      tag "existential" ["type",typ t;"binder",str binder;"predicate",expr (depth+1) (predicate binder)]
  | BinaryExp (a,b,op) -> tag (binary op) ["left",expr depth a;"right",expr depth b]
  | UnaryExp (a,op) -> tag (match op with Not->"not" | Neg->"neg") ["value",expr depth a]
  | ProductExp xs -> tag "product" ["values",arr (List.map (expr depth) xs)]
  | _ -> failwith "Unsupported knowledge-base expression in diagnostic serializer"
let value = function Parsed x -> parsed x | Target x -> expr 0 x
let dest = function
  | Absolute x -> tag "absolute" ["value",value x]
  | InHome (user,x) -> tag "in_home" ["user",str user;"value",value x]
let path = function
  | Remote d -> tag "remote" ["destination",dest d]
  | Controller d -> tag "controller" ["destination",dest d]
let paths = function
  | InPath p -> tag "in_path" ["path",path p]
  | Glob {base;glob} -> tag "glob" ["base",path base;"glob",str glob]
let perm (p:perm) = obj ["owner",bool p.owner;"group",bool p.group;"other",bool p.other]
let perms (p:file_perms) = obj ["read",opt perm p.read;"write",opt perm p.write;
  "execute",opt perm p.exec;"list_directory",opt perm p.file_list;
  "setuid",opt bool p.setuid;"setgid",opt bool p.setgid;"sticky",opt bool p.sticky]
let file (d:file_desc) = obj ["path",path d.path;"owner",opt parsed d.owner;
  "group",opt parsed d.group;"permissions",perms d.perms]
let files (d:files_desc) = obj ["paths",paths d.paths;"owner",opt parsed d.owner;
  "group",opt parsed d.group;"permissions",perms d.perms]
let manager = function
  | System -> str "system" | Apt -> str "apt" | Dnf -> str "dnf"
  | Pip env -> tag "pip" ["environment",opt parsed env]
let pkg ps = arr (List.map (fun (p:pkg_spec)->obj ["name",str p.name;"manager",manager p.pkg_manager]) ps)
let account = function User s->tag "user" ["name",str s] | Group s->tag "group" ["name",str s]
let cond = function
  | CheckOs os -> tag "os" ["value",str (match os with Debian->"Debian" | Ubuntu->"Ubuntu" | RedHat->"RedHat" | DebianFamily->"DebianFamily" | RedHatFamily->"RedHatFamily")]
  | FileExists p -> tag "file_exists" ["path",path p]
  | DirExists p -> tag "directory_exists" ["path",path p]
  | PkgInstalled p -> tag "package_installed" ["packages",pkg p]
  | ServiceRunning s -> tag "service_running" ["name",expr 0 s]
let action = function
  | CloneGitRepo {repo;version;dest} -> tag "clone" ["repository",expr 0 repo;"version",opt parsed version;"destination",file dest]
  | CopyDir {src;dest} -> tag "copy_directory" ["source",path src;"destination",file dest]
  | CopyFile {src;dest} -> tag "copy_file" ["source",path src;"destination",file dest]
  | CopyFiles {src;dest} -> tag "copy_files" ["source",paths src;"destination",files dest]
  | CreateDir {dest} -> tag "create_directory" ["destination",file dest]
  | CreateFile {dest;content} -> tag "create_file" ["destination",file dest;"content",opt str content]
  | CreateGroup {name} -> tag "create_group" ["name",str name]
  | CreateSshKey {loc} -> tag "create_ssh_key" ["path",path loc]
  | CreateUser {name;group;groups} -> tag "create_user" ["name",str name;"primary_group",opt str group;"supplemental_groups",opt (fun xs->arr(List.map str (List.sort String.compare xs))) groups]
  | CreateVirtualEnv {version;loc} -> tag "create_virtualenv" ["version",opt str version;"path",path loc]
  | DeleteDir {loc} -> tag "delete_directory" ["path",path loc]
  | DeleteFile {loc} -> tag "delete_file" ["path",path loc]
  | DeleteFiles {loc} -> tag "delete_files" ["paths",paths loc]
  | DeleteGroup {name} -> tag "delete_group" ["name",str name]
  | DeleteUser {name} -> tag "delete_user" ["name",str name]
  | DisablePassword {user} -> tag "disable_password" ["user",str user]
  | DisableSudo {who;passwordless} -> tag "disable_sudo" ["account",account who;"passwordless",bool passwordless]
  | DownloadFile {dest;src} -> tag "download" ["source",str src;"destination",file dest]
  | EnableSudo {who;passwordless} -> tag "enable_sudo" ["account",account who;"passwordless",bool passwordless]
  | InstallPkg {pkg=p;version} -> tag "install" ["packages",pkg p;"version",opt str version]
  | MoveDir {src;dest} -> tag "move_directory" ["source",path src;"destination",file dest]
  | MoveFile {src;dest} -> tag "move_file" ["source",path src;"destination",file dest]
  | MoveFiles {src;dest} -> tag "move_files" ["source",paths src;"destination",files dest]
  | Reboot -> tag "reboot" []
  | SetEnvVar {name;value} -> tag "set_environment" ["name",str name;"value",parsed value]
  | SetFilePerms {loc;perms=p} -> tag "set_file_permissions" ["path",path loc;"permissions",perms p]
  | SetFilesPerms {locs;perms=p} -> tag "set_files_permissions" ["paths",paths locs;"permissions",perms p]
  | SetShell {user;shell} -> tag "set_shell" ["user",str user;"shell",path shell]
  | StartService {name} -> tag "start_service" ["name",expr 0 name]
  | StopService {name} -> tag "stop_service" ["name",expr 0 name]
  | UninstallPkg {pkg=p} -> tag "uninstall" ["packages",pkg p]
  | WriteFile {str=s;dest;position} -> tag "write_file" ["value",parsed s;"destination",file dest;"position",str (match position with Top->"top" | Bottom->"bottom" | Overwrite->"overwrite")]
let rec sequence = function
  | End -> [] | Atom a -> [action a]
  | Seq (a,b) -> let first=sequence a in first @ sequence b
  | Cond (c,t,e) ->
      let c=cond c in let t=sequence t in let e=sequence e in
      [tag "conditional" ["condition",c;"then",arr t;"else",arr e]]
let () =
  try
    let input=In_channel.with_open_text Sys.argv.(1) In_channel.input_all in
    let parsed=Fql.Parser.query Fql.Lexer.token (Lexing.from_string input) in
    if parsed=[] then (print_endline (obj ["status",str "empty_query"]); exit 10);
    match S.analyze_top parsed with
    | Error e -> print_endline(obj ["status",str "semantic_error";"error",str e]); exit 11
    | Ok q -> print_endline(obj ["status",str "ok";"effects",arr (sequence q)])
  with e -> print_endline(obj ["status",str "diagnostic_error";"error",str (Printexc.to_string e)]); exit 12
