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

let make_args args : Ast.args = Some (Hashtbl.of_seq (List.to_seq args))

let extract_arg (t: Ast.args) (k: string) : 'a option =
  match t with
  | None -> None
  | Some t ->
      match Hashtbl.find_opt t [Str k] with
      | None -> None
      | Some v -> Hashtbl.remove t [Str k]; Some v

let extract (t: ('a, 'b) Hashtbl.t option) (k: 'a) : 'b option =
  match t with
  | None -> None
  | Some t ->
      match Hashtbl.find_opt t k with
      | None -> None
      | Some v -> Hashtbl.remove t k; Some v

let args_empty (t: Ast.args) : bool =
  match t with
  | None -> true
  | Some t -> Hashtbl.length t = 0

let args_to_string (t: Ast.args) : string =
  match t with
  | None -> ""
  | Some t ->
      String.concat ", " (List.map 
        (fun (x, y) -> Printf.sprintf "%s = %s" (ParseTree.unparse_vals x)
                                                (ParseTree.unparse_vals y))
        (List.of_seq (Hashtbl.to_seq t)))

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


let init_context : Knowledge.context = { os = None }

let refine_context_os ctx os =
  let refine_os ctx os =
    match ctx with
    | None -> Some [os]
    | Some ctx -> if List.mem os ctx then Some [os] else Some []
  in { os = refine_os ctx.os os }

let refine_context_not_os ctx os =
  let refine_os ctx os =
    match ctx with
    | None -> None
    | Some ctx -> Some (list_rem ctx os)
  in { os = refine_os ctx.os os }

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

  let extract_file_perms (args: Ast.args) : (Ast.file_perms, string) result =
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

  let extract_file_info (args: Ast.args) : (file_info, string) result =
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
        if lhs = [Str "os"]
        then let os : (Ast.ansible_os, string) result =
          match rhs with
          | [Str "Debian"] -> Ok Debian
          | [Str "Ubuntu"] -> Ok Ubuntu
          | [Str "RedHat"] -> Ok RedHat
          | _ -> Error (Printf.sprintf "Unknown OS: %s"
                                       (ParseTree.unparse_vals rhs))
        in Result.bind os (fun os ->
          Result.bind (analyze_base (refine_context_os ctx os) t) (fun t ->
            Result.bind (analyze_base (refine_context_not_os ctx os) e)
              (fun e -> Ok (Ast.Cond (Ast.CheckOs os, t, e)))))
        else Error (Printf.sprintf "Unhandled equality check between %s and %s"
                     (ParseTree.unparse_vals lhs) (ParseTree.unparse_vals rhs))
    | Exists desc ->
        begin match desc with
        | Str "file" :: path ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.FileExists p, t, e)))))
        | Str "directory" :: path ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.DirExists p, t, e)))))
        | _ ->
            let (last, rest) = list_last desc
            in match last with
            | Str "file" ->
                Result.bind (Knowledge.fileDef ctx rest None) (fun p ->
                  Result.bind (analyze_base ctx t) (fun t ->
                    Result.bind (analyze_base ctx e) (fun e ->
                      Ok (Ast.Cond (Ast.FileExists p, t, e)))))
            | Str "directory" ->
                Result.bind (Knowledge.dirDef ctx rest None) (fun p ->
                  Result.bind (analyze_base ctx t) (fun t ->
                    Result.bind (analyze_base ctx e) (fun e ->
                      Ok (Ast.Cond (Ast.DirExists p, t, e)))))
            | _ -> Error (Printf.sprintf "cannot check existance of: %s"
                            (ParseTree.unparse_vals desc))
        end
    | Required desc ->
        Result.bind (Knowledge.requirementDef ctx desc) (fun c ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (c, t, e)))))
    | Installed desc ->
        Result.bind (Knowledge.pkgDef ctx desc None) (fun pkg ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (PkgInstalled pkg, t, e)))))
    | Running desc ->
        Result.bind (Knowledge.serviceDef ctx desc None) (fun nm ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (ServiceRunning nm, t, e)))))

  and analyze_atom (ctx: context) (a: ParseTree.atom)
    : (Ast.act, string) result =
    let (act, args) = a
    in let args = make_args args
    in match act with
    | Clone vs ->
        let (last, rest) = list_last vs
        in if last = Str "repository"
        then Result.bind (Knowledge.repoDef ctx rest args) (fun repo ->
          match extract_arg args "into" with
          | None -> Error "Clone requires 'into' argument with target directory"
          | Some p -> Result.bind (analyze_path p) (fun p ->
              Result.bind (extract_file_info args) (fun file_info ->
                if args_empty args
                then 
                  Ok (Ast.CloneRepo {
                      files = repo.files; contents = repo.contents;
                      dest = { path = p; owner = file_info.owner;
                               group = file_info.group;
                               perms = file_info.perms }})
                else Error (Printf.sprintf "Unhandled arguments for clone: %s"
                                            (args_to_string args)))))
        else Error (Printf.sprintf "Unsure how to clone: %s"
                      (ParseTree.unparse_vals vs))
    | _ -> Error "TODO"

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
