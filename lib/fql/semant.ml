(* We'll use a semantic analysis phase to ensure that appropriate arguments and
 * categories are selected and we'll produce a new query AST incorporating the
 * info for easy code generation.
 *
 * The goal of this analysis is to normalize the query into a form in which
 * a signle action will always be translated in mostly the same way to the
 * module language (with certain expressions possibly depending on the
 * knowledge base).
 *)

type path = Remote of string | Controller of string

type ansible_os = Debian | Ubuntu | RedHat

type path_desc = AtPath    of path
               | TextDesc  of string
type paths_desc = InPath   of path
                | Glob     of { base: path; glob: string }
                | TextDesc of string

type perm = { owner: bool; group: bool; other: bool }
type file_perms = { read: perm option; write: perm option; exec: perm option;
                    file_list: perm option; setuid: bool option;
                    setgid: bool option; sticky: bool option }
type file_desc = { path: path_desc option; owner: string option;
                   group: string option; perms: file_perms }

type file_pos = Top | Bottom

type account_desc = User  of string
                  | Group of string

type condition = CheckOs    of ansible_os
               | RequiresRestart
               | FileExists of path_desc
               | DirExists  of path_desc
               | And        of condition * condition
               | Or         of condition * condition
               | Not        of condition

type act = CloneRepo        of { repo: string; name: string; dest: file_desc }

         | CopyDir          of { src: file_desc; dest: file_desc }
         | CopyFile         of { src: file_desc; dest: file_desc }
         | CopyFiles        of { src: paths_desc; dest: file_desc }

         | CreateDir        of { dest: file_desc }
         | CreateFile       of { dest: file_desc; content: string option }
         | CreateGroup      of { name: string }
         | CreateSshKey     of { user: string; loc: path option }
         | CreateUser       of { name: string; group: string option;
                                 groups: string list }
         | CreateVirtualEnv of { version: string; loc: path }

         | DeleteDir        of { loc: path_desc }
         | DeleteFile       of { loc: path_desc }
         | DeleteFiles      of { loc: paths_desc }
         | DeleteGroup      of { name: string }
         | DeleteUser       of { name: string }

         | DisablePassword  of { user: string }
         | DisableSudo      of { who: account_desc; passwordless: bool }

         | DownloadFile     of { dest: file_desc; src: string }

         | EnableSudo       of { who: account_desc; passwordless: bool }

         | InstallPkg       of { desc: string; version: string option;
                                 within: string option; loc: path option }

         | MoveDir          of { src: file_desc; dest: file_desc }
         | MoveFile         of { src: file_desc; dest: file_desc }
         | MoveFiles        of { src: paths_desc; dest: file_desc }

         | Restart

         | SetEnvVar        of { name: string; value: string }
         | SetFilePerms     of { loc: path_desc; perms: file_perms }
         | SetFilesPerms    of { locs: paths_desc; perms: file_perms }
         | SetShell         of { user: string; shell: string }

         | StartService     of { name: string }

         | StopService      of { name: string }

         | UninstallPkg     of { desc: string;
                                 within: string option; loc: path option }

         | WriteFile        of { str: string; dest: file_desc;
                                 position: file_pos }

type query = End
           | Atom of act
           | Seq  of query * query
           | Cond of condition * query * query

let extract (t: ('a, 'b) Hashtbl.t) (k: 'a) : 'b option =
  match Hashtbl.find_opt t k with
  | None -> None
  | Some v -> Hashtbl.remove t k; Some v

let rec list_last xs =
  match xs with
  | [] -> failwith "cannot compute last element of empty list"
  | [x] -> (x, [])
  | x :: xs ->
      let (l, rest) = list_last xs
      in (l, x :: rest)

let flatten xs = String.concat " " xs

let analyze_path (p: string list) : (path, string) result =
  match p with
  | [s] | ["remote"; s] -> Ok (Remote s)
  | ["controller"; s] -> Ok (Controller s)
  | _ -> Error (Printf.sprintf "unhandled path specifier '%s'" 
                    (String.concat " " p))

let rec analyze_cond (c: Ast.cond) : (condition, string) result =
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
        | ["Debian"] -> Ok (CheckOs Debian)
        | ["Ubuntu"] -> Ok (CheckOs Ubuntu)
        | ["RedHat"] -> Ok (CheckOs RedHat)
        | _ -> Error (Printf.sprintf "Unknown OS '%s'" (String.concat " " rhs))
      else Error (Printf.sprintf "Unhandled equality check between %s and %s"
                              (String.concat " " lhs) (String.concat " " rhs))
  | Exists desc ->
      begin match desc with
      | "file" :: path ->
          Result.map (fun p -> FileExists (AtPath p)) (analyze_path path)
      | "directory" :: path -> 
          Result.map (fun p -> DirExists (AtPath p)) (analyze_path path)
      | _ ->
          let (last, rest) = list_last desc
          in let rest = flatten rest
          in if last = "file" then Ok (FileExists (TextDesc rest))
          else if last = "directory" then Ok (DirExists (TextDesc rest))
          else Error (Printf.sprintf "cannot check existance of: %s"
                        (String.concat " " desc))
      end
  | Required desc ->
      begin match desc with
      | "restart" :: [] -> Ok RequiresRestart
      | _ -> Error (Printf.sprintf "cannot check requirement of: %s"
                      (String.concat " " desc))
      end

type file_or_dir = File | Dir

let analyze_atom (a: Ast.atom) : (act, string) result =
  let (act, args) = a
  in let _args = Hashtbl.of_seq (List.to_seq
    (List.map (fun (a, v) -> (String.concat " " a, v)) args))
  in match act with
  | _ -> Error "TODO"

let rec analyze_base (b: Ast.base) (k: query) : (query, string) result =
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

let rec analyze_top (q: Ast.top) : (query, string) result =
  match q with
  | [] -> Ok End
  | b :: q -> Result.bind (analyze_top q) (analyze_base b)
