module Target = Modules.Target.Ast_Target

type args = (ParseTree.vals, ParseTree.vals) Hashtbl.t option

let make_args args = Some (Hashtbl.of_seq (List.to_seq args))

let extract_arg (t: args) (k: string) : 'a option =
  match t with
  | None -> None
  | Some t ->
      match Hashtbl.find_opt t [Str k] with
      | None -> None
      | Some v -> Hashtbl.remove t [Str k]; Some v

let rec list_last xs =
  match xs with
  | [] -> failwith "cannot compute last element of empty list"
  | [x] -> (x, [])
  | x :: xs ->
      let (l, rest) = list_last xs
      in (l, x :: rest)

let rec list_rem xs y =
  match xs with
  | [] -> []
  | x :: xs -> if x = y then xs else x :: list_rem xs y

type path = Remote of ParseTree.value | Controller of ParseTree.value
type paths = AtPath   of path
           | InPath   of path
           | Glob     of { base: path; glob: string }

type ansible_os = Debian | Ubuntu | RedHat

type pkg = { name: string; pkg_manager: string }

type cond = CheckOs         of ansible_os
          | FileExists      of path
          | DirExists       of path
          | PkgInstalled    of pkg
          | ServiceRunning  of string
          | And             of cond * cond
          | Or              of cond * cond
          | Not             of cond

type perm = { owner: bool; group: bool; other: bool }
type file_perms = { read: perm option; write: perm option; exec: perm option;
                    file_list: perm option; setuid: bool option;
                    setgid: bool option; sticky: bool option }
type file_desc = { path: path; owner: string option;
                   group: string option; perms: file_perms }

type file_pos = Top | Bottom

type account_desc = User  of string
                  | Group of string


type act = CloneRepo        of { files: Target.expr;
                                 contents: Target.expr -> Target.expr;
                                 dest: file_desc }

         | CopyDir          of { src: path; dest: file_desc }
         | CopyFile         of { src: path; dest: file_desc }
         | CopyFiles        of { src: paths; dest: file_desc }

         | CreateDir        of { dest: file_desc }
         | CreateFile       of { dest: file_desc; content: string option }
         | CreateGroup      of { name: string }
         | CreateSshKey     of { user: string; loc: path option }
         | CreateUser       of { name: string; group: string option;
                                 groups: string list }
         | CreateVirtualEnv of { version: string; loc: path }

         | DeleteDir        of { loc: path }
         | DeleteFile       of { loc: path }
         | DeleteFiles      of { loc: paths }
         | DeleteGroup      of { name: string }
         | DeleteUser       of { name: string }

         | DisablePassword  of { user: string }
         | DisableSudo      of { who: account_desc; passwordless: bool }

         | DownloadFile     of { dest: file_desc; src: string }

         | EnableSudo       of { who: account_desc; passwordless: bool }

         | InstallPkg       of { pkgs: string list; version: string option;
                                 within: string option; loc: path option }

         | MoveDir          of { src: path; dest: file_desc }
         | MoveFile         of { src: path; dest: file_desc }
         | MoveFiles        of { src: paths; dest: file_desc }

         | Restart

         | SetEnvVar        of { name: string; value: string }
         | SetFilePerms     of { loc: path; perms: file_perms }
         | SetFilesPerms    of { locs: paths; perms: file_perms }
         | SetShell         of { user: string; shell: string }

         | StartService     of { name: string }

         | StopService      of { name: string }

         | UninstallPkg     of { pkgs: string list; within: string option;
                                 loc: path option }

         | WriteFile        of { str: string; dest: file_desc;
                                 position: file_pos }

type query = End
           | Atom of act
           | Seq  of query * query
           | Cond of cond * query * query
