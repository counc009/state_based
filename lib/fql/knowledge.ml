open Ast
open Utils

type gitRepoInfo = { repo: string; version: ParseTree.value option }

module type Knowledge_Base = sig
  val gitRepoDef : context -> ParseTree.vals -> args
                                             -> (gitRepoInfo, string) result

  val fileDef : context -> ParseTree.vals -> args -> (path, string) result
  val filesDef : context -> ParseTree.vals -> args -> (paths, string) result
  val dirDef : context -> ParseTree.vals -> args -> (path, string) result

  val requirementDef : context -> ParseTree.vals -> args
                                                 -> (Ast.cond, string) result

  val pkgDef : context -> ParseTree.vals -> args -> (Ast.pkg, string) result
  val serviceDef : context -> ParseTree.vals -> args -> (string, string) result
end

module Example : Knowledge_Base = struct
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
                    Ok (Printf.sprintf "https://github.com/%s/%s.git" org repo)
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
            | Some [Str nm] -> Ok nm
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

  let fileDef _ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str "postfix"; Str "configuration"] -> Ok (Remote (Str "/etc/postfix/main.cf"))
    | [Str "apache"; Str "server"; Str "html"; Str "home"; Str "page"]
      -> Ok (Remote (Str "/var/www/html/index.html"))
    | [Str "apache"; Str "server"; Str "php"; Str "home"; Str "page"]
      -> Ok (Remote (Str "/var/www/html/index.php"))
    | [Str "bash"; Str "configuration"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for bash configuration file"
        | Some [Str nm] -> Ok (Remote (Str (Printf.sprintf "/home/%s/.bashrc" nm)))
        | Some vs -> Error (Printf.sprintf
            "For bash configuration file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "zsh"; Str "configuration"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for zsh configuration file"
        | Some [Str nm] -> Ok (Remote (Str (Printf.sprintf "/home/%s/.zshrc" nm)))
        | Some vs -> Error (Printf.sprintf
            "For zsh configuration file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "bashrc"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for bashrc file"
        | Some [Str nm] -> Ok (Remote (Str (Printf.sprintf "/home/%s/.bashrc" nm)))
        | Some vs -> Error (Printf.sprintf
            "For bashrc file, expected single name for 'user', found: %s"
            (ParseTree.unparse_vals vs))
        end
    | [Str "zshrc"] ->
        begin match extract_arg args "user" with
        | None -> Error "Must specify 'user' for zshrc file"
        | Some [Str nm] -> Ok (Remote (Str (Printf.sprintf "/home/%s/.zshrc" nm)))
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
        | Some [Str nm] -> Ok (Remote (Str (Printf.sprintf "/home/%s/.zshrc.d" nm)))
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
        | Some Debian | Some Ubuntu ->
            Ok (FileExists (Remote (Str "/var/run/reboot-required")))
        | Some RedHat ->
            Error "Condition 'reboot required' not supported for RedHat"
        end
    | _ -> Error (Printf.sprintf "Unknown requirement: %s"
                                 (ParseTree.unparse_vals vs))

  let pkgDef ctx (vs: ParseTree.vals) args =
    match vs with
    | [Str "numpy"] ->
        let virtenv =
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
        in Result.bind virtenv (fun virtenv ->
          match virtenv with
          | Some p -> Ok { name = "numpy"; pkg_manager = Pip (Some p) }
          | None ->
              match ctx.os with
              | None -> Error "cannot handle numpy system-wide without knowing OS"
              | Some Debian | Some Ubuntu ->
                  Ok { name = "python3-numpy"; pkg_manager = Apt }
              | Some RedHat -> Ok { name = "numpy"; pkg_manager = Pip None })
    | [Str "bash"] -> Ok { name = "bash"; pkg_manager = System }
    | [Str "zsh"] -> Ok { name = "zsh"; pkg_manager = System }
    | [Str "postfix"] -> Ok { name = "postfix"; pkg_manager = System }
    | [Str "apache"] | [Str "apache"; Str "server"] | [Str "apache server"] ->
        begin match ctx.os with
        | None -> Error "cannot handle apache server without knowing OS"
        | Some Debian | Some Ubuntu -> Ok { name = "apache2"; pkg_manager = Apt }
        | Some RedHat -> Ok { name = "httpd"; pkg_manager = Dnf }
        end
    | [Str "ssh"; Str "client"] | [Str "ssh client"] ->
        begin match ctx.os with
        | None -> Error "cannot handle ssh client without knowing OS"
        | Some Debian | Some Ubuntu -> Ok { name = "ssh-client"; pkg_manager = Apt }
        | Some RedHat -> Ok { name = "ssh-clients"; pkg_manager = Dnf }
        end
    | [Str "ssh"; Str "server"] | [Str "ssh server"] ->
        Ok { name = "ssh-server"; pkg_manager = System }
    | _ -> Error (Printf.sprintf "Unknown package: %s"
                                 (ParseTree.unparse_vals vs))

  let serviceDef ctx (vs: ParseTree.vals) _args =
    match vs with
    | [Str "ssh"; Str "server"] | [Str "ssh server"] -> Ok "sshd"
    | [Str "apache"; Str "server"] | [Str "apache server"] ->
        begin match ctx.os with
        | None -> Error "cannot handle apache server service without knowing OS"
        | Some Debian | Some Ubuntu -> Ok "apache2"
        | Some RedHat -> Ok "httpd"
        end
    | [Str "postfix"] -> Ok "postfix"
    | _ -> Error (Printf.sprintf "Unknown service: %s"
                                 (ParseTree.unparse_vals vs))
end
