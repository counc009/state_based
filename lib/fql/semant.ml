(* We'll use a semantic analysis phase to ensure that appropriate arguments and
 * categories are selected and we'll produce a new query AST incorporating the
 * info for easy code generation *)

let extract (t: ('a, 'b) Hashtbl.t) (k: 'a) : 'b option =
  match Hashtbl.find_opt t k with
  | None -> None
  | Some v -> Hashtbl.remove t k; Some v

type ansible_os = Debian | Ubuntu | RedHat

(* Packages that have configuration files that we know about *)
type file_configs = Postfix
(* Packages that have configuration directories that we know about *)
type dir_configs = Zsh
(* Webservers that we are aware of and know where they store their content *)
type web_server = Apache

(* Sources of git repos we know how to handle *)
type git_repo = GitHub of string * string option (* repo name and branch *)
              | GitLab of string * string option
              | Git of string * string option (* url and branch *)

type semant_cond = CheckOS of ansible_os
                 (* TODO: More *)
                 | And of semant_cond * semant_cond
                 | Or  of semant_cond * semant_cond
                 | Not of semant_cond
type path = Remote of string | Controller of string
type file = File of path | Directory of path | ConfigFile of file_configs
          | ConfigDir of dir_configs | HomePage of web_server

type semant_atom = Backup of file * path option (* file to backup and dest *)
                 | Clone of git_repo * path (* repo and destination *)

type semant_query = End
                  | Atom of semant_atom
                  | Seq  of semant_query * semant_query
                  | Cond of semant_cond * semant_query * semant_query

let rec analyze_cond (c: Ast.cond) : (semant_cond, string) result =
  match c with
  | And (x, y) ->
      Result.bind (analyze_cond x) 
        (fun x -> Result.map (fun y -> And (x, y)) (analyze_cond y))
  | Or (x, y) ->
      Result.bind (analyze_cond x) 
        (fun x -> Result.map (fun y -> Or (x, y)) (analyze_cond y))
  | Not c -> Result.map (fun c -> Not c) (analyze_cond c)
  | Eq (lhs, rhs) ->
      if lhs = ["os"]
      then match rhs with
        | ["Debian"] -> Ok (CheckOS Debian)
        | ["Ubuntu"] -> Ok (CheckOS Ubuntu)
        | ["RedHat"] -> Ok (CheckOS RedHat)
        | _ -> Error (Printf.sprintf "Unknown OS '%s'" (String.concat " " rhs))
      else Error (Printf.sprintf "Unhandled equality check between %s and %s"
                              (String.concat " " lhs) (String.concat " " rhs))
  | Exists _ -> Error "TODO"
  | Required _ -> Error "TODO"

(* valid atoms require that sufficient context be given for the action and the
   context it requires:

 - backup <backupable> [to <path>]
 - clone <cloneable> into <path>
 - copy <copyable> to=<path>
 - create <creatable>
 - delete <deleteable>
 - disable <disableable>
 - download <downloadable> from=<url>
 - enable <enableable>
 - ensure <ensurable>
 - install <string list> [version = <string>] <installation-target>
 - move <copyable> to=<path>
 - restart
 - set <setable>
 - start <startable>
 - stop <startable>
 - uninstall <string list>
 - write <string> to=<path> position=<string>

<backupable> ::= <file>
<cloneable>  ::= github repo with name=<string> [branch=<string>]
               | github repository with name=<string> [branch=<string>]
               | gitlab repo with name=<string> [branch=<string>]
               | gitlab repository with name=<string> [branch=<string>]
               | git repo at <url> [with branch=<string>]
               | git repository at <url> [with branch=<string>]
<copyable>  ::= file from <path>
              | directory from <path>
              | files [with glob=<string>] from <path>
              | <file>
<creatable> ::= <file> [with content=<string>]
              | virtual environment [with python=<string>] at <path>
              | user with name=<string> [with group=<string>] [with password=<string>]
              | group with name=<string>
              | ssh key at <path> with user=<string>
<deleteable> ::= <file>
               | virtual environment in <path>
               | user with name=<string>
               | group with name=<string>
               | files in <path>
<disableable> ::= password with user=<string>
                | sudo with user=<string>
                | sudo with group=<string>
<downloadable> ::= file to <path>
                 | postfix configuration file
                 | apache server home page
<enableable> ::= password with password=<string>, user=<string>
               | [passwordless] sudo with user=<string>
               | [passwordless] sudo with group=<string>
<setable> ::= default shell with user=<string> to <string>
            | environment variable <string> to <string>
            | file permissions of <file-kind> with path=<path>, [read=<string>],
                [write=<string>], [execute=<string>], [list directory=<string>],
                [setuid=<string>], [setgid=<string>], [sticky=<string>]
<startable> ::= <string> service

<file> ::= file at <path>
         | directory at <path>
         | postfix configuration file
         | zsh configuration directory
         | apache server home page
<installation-target> ::= ε
                        | in virtual environment at <path>
<path> ::= <string>
         | controller <string>
         | remote <string>
<string list> ::= <string>
                | <string> and <string>
                | <string>, and <string>
                | <string>, <string list>
*)

let analyze_path (p: string list) : (path, string) result =
  match p with
  | [s] | ["remote"; s] -> Ok (Remote s)
  | ["controller"; s] -> Ok (Controller s)
  | _ -> Error (Printf.sprintf "unhandled path specifier '%s'" 
                    (String.concat " " p))

let analyze_file (desc: string list) (args: (string, string list) Hashtbl.t)
  : (file, string) result =
  match desc with
  | ["file"] ->
      begin match extract args "at" with
      | None -> Error "missing argument 'at' for file"
      | Some p -> Result.map (fun p -> File p) (analyze_path p)
      end
  | ["directory"] ->
      begin match extract args "at" with
      | None -> Error "missing argument 'at' for directory"
      | Some p -> Result.map (fun p -> Directory p) (analyze_path p)
      end
  | ["postfix"; "configuration"; "file"] -> Ok (ConfigFile Postfix)
  | ["zsh"; "configuration"; "directory"] -> Ok (ConfigDir Zsh)
  | ["apache"; "server"; "home"; "page"] -> Ok (HomePage Apache)
  | _ -> Error (Printf.sprintf "unknown file kind: %s" (String.concat " " desc))

let analyze_atom (a: Ast.atom) : (semant_atom, string) result =
  let (action, args) = a
  in let args 
    = Hashtbl.of_seq 
        (List.to_seq 
          (List.map (fun (a, v) -> (String.concat " " a, v)) args))
  in match action with
  | Backup vs -> Result.bind (analyze_file vs args)
      (fun file -> match extract args "to" with
        | None when Hashtbl.length args = 0 -> Ok (Backup (file, None))
        | Some p when Hashtbl.length args = 0 ->
            Result.bind (analyze_path p) (fun p -> Ok (Backup (file, Some p)))
        | _ -> Error (Printf.sprintf "unsupported arguments for backup: %s"
                          (String.concat ", " 
                            (List.map
                              (fun (a, v) -> a ^ "=" ^ String.concat " " v)
                              (List.of_seq (Hashtbl.to_seq args))))))
  | Clone vs ->
      let repo = 
        match vs with
        | ["github"; "repo"] | ["github"; "repository"] ->
            begin match extract args "name" with
            | None -> Error "github repo requires 'name' argument"
            | Some [nm] ->
                begin match extract args "branch" with
                | None -> Ok (GitHub (nm, None))
                | Some [b] -> Ok (GitHub (nm, Some b))
                | Some _ -> Error "git branch name must be a single value"
                end
            | Some _ -> Error "github repo requires a single 'name' value"
            end
        | ["gitlab"; "repo"] | ["gitlab"; "repository"] ->
            begin match extract args "name" with
            | None -> Error "gitlab repo requires 'name' argument"
            | Some [nm] ->
                begin match extract args "branch" with
                | None -> Ok (GitLab (nm, None))
                | Some [b] -> Ok (GitLab (nm, Some b))
                | Some _ -> Error "git branch name must be a single value"
                end
            | Some _ -> Error "gitlab repo requires a single 'name' value"
            end
        | ["git"; "repo"] | ["git"; "repository"] -> 
            begin match extract args "at" with
            | None -> Error "git repo requires 'at' argument"
            | Some [nm] -> 
                begin match extract args "branch" with
                | None -> Ok (Git (nm, None))
                | Some [b] -> Ok (Git (nm, Some b))
                | Some _ -> Error "git branch name must be a single value"
                end
            | Some _ -> Error "git repo requires a single 'at' value"
            end
          | _ -> Error (Printf.sprintf "Unknown how to clone: %s"
                            (String.concat " " vs))
      in Result.bind repo
        (fun repo ->
          match extract args "into" with
          | None -> Error "Clone must specify where to clone into"
          | Some p when Hashtbl.length args = 0 ->
              Result.bind (analyze_path p) (fun p -> Ok (Clone (repo, p)))
          | _ -> Error (Printf.sprintf "unsupported arguments for clone: %s"
                        (String.concat ", "
                          (List.map
                            (fun (a, v) -> a ^ "=" ^ String.concat " " v)
                            (List.of_seq (Hashtbl.to_seq args))))))
  | _ -> Error "TODO"

(* Post semantic analysis the verbs should each perform the same action in the
   module language, with differences on certain holes (probably expressions)
   that are filled from the knowledge base.
   So, for instance, we might want to have
   - CreateUser
   - CreateGroup
   - CreateFile [including configuration files]
   - CreateDirectory [including configuration directories]
   - ...
*)

let rec analyze_base (b: Ast.base) (k: semant_query)
  : (semant_query, string) result =
  match b with
  | Nil -> Ok k
  | Cons (a, b) ->
      Result.bind (analyze_atom a)
        (fun a -> Result.map (fun q -> Seq (Atom a, q)) (analyze_base b k))
  | If (c, t, e) ->
      Result.bind (analyze_cond c)
        (fun c -> Result.bind (analyze_base t End)
          (fun t -> Result.bind (analyze_base e End)
            (fun e -> Ok (Seq (Cond (c, t, e), k)))))

let rec analyze_top (q: Ast.top) : (semant_query, string) result =
  match q with
  | [] -> Ok End
  | b :: q -> Result.bind (analyze_top q) (analyze_base b)
