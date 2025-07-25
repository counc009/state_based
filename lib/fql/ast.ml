type dest = Value of ParseTree.value | InHome of string * ParseTree.value
type path = Remote of dest | Controller of dest

type paths = InPath   of path
           | Glob     of { base: path; glob: string }

type ansible_os = Debian | Ubuntu | RedHat | DebianFamily | RedHatFamily

(* For pip we optionally specify a virtual environment to install in *)
type package_manager = System | Apt | Dnf | Pip of ParseTree.value option

type pkg = { name: string; pkg_manager: package_manager }

type cond = CheckOs         of ansible_os
          | FileExists      of path
          | DirExists       of path
          | PkgInstalled    of pkg
          | ServiceRunning  of string

type perm = { mutable owner: bool; mutable group: bool; mutable other: bool }
type file_perms = { read: perm option; write: perm option; exec: perm option;
                    file_list: perm option; setuid: bool option;
                    setgid: bool option; sticky: bool option }
type file_desc = { path: path; owner: ParseTree.value option;
                   group: ParseTree.value option; perms: file_perms }

type files_desc = { paths: paths; owner: ParseTree.value option;
                    group: ParseTree.value option; perms: file_perms }

type file_pos = Top | Bottom | Overwrite

type account_desc = User  of string
                  | Group of string


type act = CloneGitRepo     of { repo: string; version: ParseTree.value option;
                                 dest: file_desc }

         | CopyDir          of { src: path; dest: file_desc }
         | CopyFile         of { src: path; dest: file_desc }
         | CopyFiles        of { src: paths; dest: files_desc }

         | CreateDir        of { dest: file_desc }
         | CreateFile       of { dest: file_desc; content: string option }
         | CreateGroup      of { name: string }
         | CreateSshKey     of { loc: path }
         | CreateUser       of { name: string; group: string option;
                                 groups: string list option }
         | CreateVirtualEnv of { version: string option; loc: path }

         | DeleteDir        of { loc: path }
         | DeleteFile       of { loc: path }
         | DeleteFiles      of { loc: paths }
         | DeleteGroup      of { name: string }
         | DeleteUser       of { name: string }

         | DisablePassword  of { user: string }
         | DisableSudo      of { who: account_desc; passwordless: bool }

         | DownloadFile     of { dest: file_desc; src: string }

         | EnableSudo       of { who: account_desc; passwordless: bool }

         | InstallPkg       of { pkg: pkg; version: string option }

         | MoveDir          of { src: path; dest: file_desc }
         | MoveFile         of { src: path; dest: file_desc }
         | MoveFiles        of { src: paths; dest: files_desc }

         | Reboot

         (* TODO: Should support setting an environment variable locally, say
          * by adding it to a user's .profile *)
         | SetEnvVar        of { name: string; value: ParseTree.value }
         | SetFilePerms     of { loc: path; perms: file_perms }
         | SetFilesPerms    of { locs: paths; perms: file_perms }
         | SetShell         of { user: string; shell: path }

         | StartService     of { name: string }

         | StopService      of { name: string }

         | UninstallPkg     of { pkg: pkg }

         | WriteFile        of { str: ParseTree.value; dest: file_desc;
                                 position: file_pos }

type query = End
           | Atom of act
           | Seq  of query * query
           | Cond of cond * query * query
