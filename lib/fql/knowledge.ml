open Ast
open Utils

let ( let^ ) = Result.bind

module Target = Modules.Ast

module type KB = sig
  val gitRepoDef : context -> ParseTree.vals -> args
                                             -> (gitRepoInfo, string) result

  val fileDef : context -> ParseTree.vals -> args -> (path, string) result
  val filesDef : context -> ParseTree.vals -> args -> (paths, string) result
  val dirDef : context -> ParseTree.vals -> args -> (path, string) result

  val requirementDef : context -> ParseTree.vals -> args
                                                 -> (Ast.cond, string) result

  val pkgDef : context -> ParseTree.vals -> args -> (Ast.pkg, string) result
  val programLoc : context -> ParseTree.vals -> args -> (path, string) result
  val serviceDef : context -> ParseTree.vals -> args -> (Target.expr, string) result
end

module Example : KB = struct
  (* Generates an existential value of a given type that takes on one of a
   * certain list of values *)
  let existential_some (t : Target.typ) (vs : Target.expr list) : Target.expr =
    let pred nm : Target.expr =
      List.fold_left
        (fun cond v -> Target.BinaryExp (BinaryExp (Id nm, v, Eq), cond, Or))
        (BoolLit false) vs
    in GenExistential (t, pred)

  let gitRepoDef _ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str ("github" as ty)] | [Str ("git" as ty)] ->
        let repo =
          if ty = "github"
          then match extract_arg args "name" with
            | None -> Error "For github repository, expected 'name' argument"
            | Some [Str nm] ->
                begin match String.split_on_char '/' nm with
                | [org; repo] ->
                    (* It seems tht the .git is optional for github, hence we
                     * use an approprate GenExistential *)
                    begin match extract_arg args "via" with
                    | Some [Str "ssh"] ->
                        let repo_base =
                          Printf.sprintf "git@github.com:%s/%s" org repo
                        in let repo_vals : Target.expr list =
                          [StringLit repo_base; StringLit (repo_base ^ ".git")]
                        in Ok (existential_some String repo_vals)
                    | Some [Str "https"] | None ->
                        let repo_base =
                          Printf.sprintf "https://github.com/%s/%s" org repo
                        in let repo_vals : Target.expr list =
                          [StringLit repo_base; StringLit (repo_base ^ ".git")]
                        in Ok (existential_some String repo_vals)
                    | Some vs -> Error (Printf.sprintf
                      "For github repository, expectd 'ssh' or 'https' for 'via' argument, found: %s"
                      (ParseTree.unparse_vals vs))
                    end
                | _ -> Error (Printf.sprintf
                  "For github repository, expected 'name' of form <org>/<repo>, found: %s"
                  nm)
                end
            | Some vs ->
                Error (Printf.sprintf
                  "For github repository, expected single 'name' value, found: %s"
                  (ParseTree.unparse_vals vs))
          else match extract_arg args "from" with
            | None -> Error "For git repository, expected 'from' argument"
            | Some [Str nm] -> Ok (StringLit nm)
            | Some vs ->
                Error (Printf.sprintf
                  "For git repository, expected single 'from' value, found: %s"
                  (ParseTree.unparse_vals vs))
        in let branch =
          match extract_arg args "branch" with
          | None -> Ok None
          | Some [v] -> Ok (Some v)
          | Some vs ->
              Error (Printf.sprintf
                "For %s repository, expected single 'branch' value, found %s"
                ty (ParseTree.unparse_vals vs))
        in let tag = 
          match extract_arg args "tag" with
          | None -> Ok None
          | Some [v] -> Ok (Some v)
          | Some vs ->
              Error (Printf.sprintf
                "For %s repository, expected single 'tag' value, found %s"
                ty (ParseTree.unparse_vals vs))
        in let version =
          Result.bind branch (fun branch ->
            Result.bind tag (fun tag ->
              match branch, tag with
              | Some _, Some _ ->
                  Error (Printf.sprintf
                    "For %s repository, expected at most one of 'branch' and 'tag'"
                    ty)
              | Some v, None | None, Some v -> Ok (Some v)
              | None, None -> Ok None))
        in Result.bind repo (fun repo ->
            Result.bind version (fun version ->
              Ok { repo = repo; version = version }))
    | _ -> Error (Printf.sprintf "Unsupported repository type: %s"
                                 (ParseTree.unparse_vals vs))

  let remote_path (s : string) : Ast.path = Remote (Absolute (Parsed (Str s)))

  let remote_path_options (ps : string list) : Ast.path =
    Remote (Absolute (Target (
      existential_some Target.Path
        (List.map (fun s -> Target.PathLit s) ps))))

  let fileDef _ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str "postfix"; Str "configuration"]
      -> Ok (remote_path "/etc/postfix/main.cf")
    | [Str "apache"; Str "server"; Str "html"; Str "home"; Str "page"]
      -> Ok (remote_path "/var/www/html/index.html")
    | [Str "apache"; Str "server"; Str "php"; Str "home"; Str "page"]
      -> Ok (remote_path "/var/www/html/index.php")
    | [Str "bash"; Str "configuration"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for bash configuration file"
        | Some [Str nm] -> Ok (Remote (InHome (nm, Parsed (Str ".bashrc"))))
        | Some vs -> Error (Printf.sprintf
            "For bash configuration file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "zsh"; Str "configuration"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for zsh configuration file"
        | Some [Str nm] -> Ok (Remote (InHome (nm, Parsed (Str ".zshrc"))))
        | Some vs -> Error (Printf.sprintf
            "For zsh configuration file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "bashrc"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for bashrc file"
        | Some [Str nm] -> Ok (Remote (InHome (nm, Parsed (Str ".bashrc"))))
        | Some vs -> Error (Printf.sprintf
            "For bashrc file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "zshrc"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for zshrc file"
        | Some [Str nm] -> Ok (Remote (InHome (nm, Parsed (Str ".zshrc"))))
        | Some vs -> Error (Printf.sprintf
            "For zshrc file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | _ -> Error (Printf.sprintf "Unknown file: %s" (ParseTree.unparse_vals vs))

  let filesDef _ctx (vs: ParseTree.vals) _args =
    Error (Printf.sprintf "Unknown files: %s" (ParseTree.unparse_vals vs))

  let dirDef _ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str "zsh"; Str "configuration"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for zsh configuration directory"
        | Some [Str nm] -> Ok (Remote (InHome (nm, Parsed (Str ".zshrc.d"))))
        | Some vs -> Error (Printf.sprintf
            "For zsh configuration directory, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | _ -> Error (Printf.sprintf "Unknown directory: %s" 
                                 (ParseTree.unparse_vals vs))

  let requirementDef (ctx: context) (vs: ParseTree.vals) _args =
    match vs with
    | [Str "reboot"] ->
        begin match ctx.os with
        | None -> Error "Condition 'reboot required' requires particular OS"
        | Some Debian | Some Ubuntu | Some DebianFamily ->
            Ok (FileExists (
              remote_path_options 
                ["/var/run/reboot-required"; "/run/reboot-required"]))
        | Some RedHat | Some RedHatFamily ->
            Error "Condition 'reboot required' not supported for RedHat"
        end
    | _ -> Error (Printf.sprintf "Unknown requirement: %s"
                                 (ParseTree.unparse_vals vs))

  (* TODO: Validate all of these packages and other possibilities *)
  let pkgDef ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str "numpy"] ->
        let^ virtenv =
          match extract_arg args "in" with
          | Some [Str "virtual"; Str "environment"]
          | Some [Str "virtual environment"] ->
              begin match extract_arg args "at" with
              | Some [p] -> Ok (Some p)
              | None -> Error "To install in virtual environment expected 'at' argument"
              | Some vs -> Error (Printf.sprintf 
                  "To install in virtual environment expected single value as path, found: %s"
                  (ParseTree.unparse_vals vs))
              end
          | _ -> Ok None
        in begin match virtenv with
        | Some p -> Ok [{ name = "numpy"; pkg_manager = Pip (Some p) }]
        | None ->
            match ctx.os with
            | None -> Error "cannot handle numpy system-wide without knowing OS"
            | Some Debian | Some DebianFamily ->
                Ok [{ name = "python3-numpy"; pkg_manager = Apt }]
            (* TODO: pip works on Ubuntu desktop but may not work on Ubuntu server *)
            | Some Ubuntu ->
                Ok [{ name = "python3-numpy"; pkg_manager = Apt };
                    { name = "numpy"; pkg_manager = Pip None }]
            | Some RedHat | Some RedHatFamily ->
                Ok [{ name = "numpy"; pkg_manager = Pip None };
                    { name = "numpy"; pkg_manager = Dnf };
                    { name = "python3-numpy"; pkg_manager = Dnf }]
        end
    | [Str "bash"] -> Ok [{ name = "bash"; pkg_manager = System }]
    | [Str "zsh"] -> Ok [{ name = "zsh"; pkg_manager = System }]
    | [Str "postfix"] -> Ok [{ name = "postfix"; pkg_manager = System }]
    | [Str "apache"] | [Str "apache"; Str "server"] | [Str "apache server"] ->
        begin match ctx.os with
        | None -> Error "cannot handle apache server without knowing OS"
        | Some Debian | Some Ubuntu | Some DebianFamily ->
            Ok [{ name = "apache2"; pkg_manager = Apt }]
        | Some RedHat | Some RedHatFamily ->
            Ok [{ name = "httpd"; pkg_manager = Dnf }]
        end
    | [Str "ssh"; Str "client"] | [Str "ssh client"] ->
        begin match ctx.os with
        | None -> Error "cannot handle ssh client without knowing OS"
        | Some Debian | Some Ubuntu | Some DebianFamily ->
            Ok [{ name = "openssh-client"; pkg_manager = Apt }]
        | Some RedHat | Some RedHatFamily ->
            Ok [{ name = "openssh-clients"; pkg_manager = Dnf }]
        end
    | [Str "ssh"; Str "server"] | [Str "ssh server"] ->
        Ok [{ name = "openssh-server"; pkg_manager = System }]
    | _ -> Error (Printf.sprintf "Unknown package: %s"
                                 (ParseTree.unparse_vals vs))

  let programLoc _ctx (vs: ParseTree.vals) _args =
    match vs with
    (* At least on Debian and RHEL, /bin is a link to /usr/bin *)
    | [Str "zsh"] -> Ok (remote_path_options ["/bin/zsh"; "/usr/bin/zsh"])
    | [Str "bash"] -> Ok (remote_path_options ["/bin/bash"; "/usr/bin/bash"])
    | _ -> Error (Printf.sprintf "Unknown executable: %s"
                                 (ParseTree.unparse_vals vs))

  let serviceDef ctx (vs: ParseTree.vals) _args
    : (Target.expr, string) result =
    match vs with
    | [Str "ssh"; Str "server"] | [Str "ssh server"] ->
        Ok (existential_some Target.String [StringLit "sshd"; StringLit "ssh"])
    | [Str "apache"; Str "server"] | [Str "apache server"] ->
        begin match ctx.os with
        | None -> Error "cannot handle apache server service without knowing OS"
        | Some Debian | Some Ubuntu | Some DebianFamily ->
            Ok (StringLit "apache2")
        | Some RedHat | Some RedHatFamily ->
            Ok (StringLit "httpd")
        end
    | [Str "postfix"] -> Ok (StringLit "postfix")
    | _ -> Error (Printf.sprintf "Unknown service: %s"
                                 (ParseTree.unparse_vals vs))
end
