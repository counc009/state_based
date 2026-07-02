let usage_msg = "runner [--users <src_file>] [--groups <src_file>] [--files <src_file>] [--reboot <hosts>] [--writes <hosts>] <query> <ansible program> -- <module definitions>"
let query = ref ""
let program = ref ""
let module_defs = ref []

let users_src = ref ""
let groups_src = ref ""
let packages_src = ref ""
let files_src = ref ""
let reboot_hosts = ref ""
let write_hosts = ref ""
let strict_files = ref ""

let cnt = ref 0
let anon_fun filename =
  (if !cnt = 0 then query := filename
  else if !cnt = 1 then program := filename
  else failwith "Only expected two anonymous arguments"); cnt := !cnt + 1

module Interp = Modules.Target.TargetInterp
module Calc = Modules.Target.Ast_Target
module Target = Modules.Target

module Semant = Fql.Semant.Semant(Fql.Knowledge.Example)

module StringSet = Fql.Heuristics.StringSet

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definitions");
   ("--users", Arg.Set_string users_src, "Validate users from a source file which is a comma-separated list of names or has lines of the form <distribution>:<comma-separated names>");
   ("--groups", Arg.Set_string groups_src, "Validate groups from a source file which is a comma-separated list of names or has lines of the form <distribution>:<comma-separated names>");
   ("--pkgs", Arg.Set_string packages_src, "Validate packages from a source file which is a comma-separated list of names or has lines of the form <distribution>:<package manager>:<comma-separated names>");
   ("--files", Arg.Set_string files_src, "Validate files from a source file which is a comma-separated list of paths or has lines of the form <distribution>:<controller/remote>:<comma-separated paths of files that exist>:<comma-separated paths of files that do not exist>");
   ("--strict-files", Arg.Set_string strict_files, "Validate files strictly");
   ("--reboot", Arg.Set_string reboot_hosts, "Validate that no reboots occur  on systems in the specified hosts unless the query reboots as well");
   ("--writes", Arg.Set_string write_hosts, "Validate that no file writes occur on systems in the specified hosts unless the query writes to that file") ]

type ('a, 'b) info_file_res =
  | All      of 'b
  | Specific of ('a * 'b) list

let parse_opts (opts : string) : StringSet.t =
  match String.split_on_char ',' opts with
  | [] | [""] -> StringSet.empty
  | lst -> Fql.Heuristics.string_set lst

let parse_info_file (single : string list -> ('a, 'b) info_file_res)
  (multi : string list -> 'a * 'b) (file : string)
  : ('a, 'b) info_file_res =
  let input = open_in file
  in let lines = In_channel.input_lines input
  in let () = close_in input

  in match lines with
  | [] -> single []
  | [l] -> single (String.split_on_char ':' l)
  | lines ->
      Specific (List.map 
        (fun line -> multi (String.split_on_char ':' line))
        lines)

let parse_dist_file = 
  let single (parts : string list) =
    match parts with
    | [] | [""] -> All StringSet.empty
    | [opts] -> All (parse_opts opts)
    | [dist; opts] -> Specific [(dist, parse_opts opts)]
    | _ -> failwith (Printf.sprintf "invalid dist option format: %s" 
              (String.concat ":" parts))
  in let multi (parts : string list) : string * StringSet.t =
    match parts with
    | [dist; opts] -> (dist, parse_opts opts)
    | _ -> failwith (Printf.sprintf "invalid dist option format: %s" 
              (String.concat ":" parts))
  in parse_info_file single multi

let parse_pkgs_file =
  let single (parts : string list) =
    match parts with
    | [] | [""] -> All StringSet.empty
    | [opts] -> All (parse_opts opts)
    | [dist; pkgmgr; opts] -> Specific [((dist, pkgmgr), parse_opts opts)]
    | _ -> failwith (Printf.sprintf "invalid pkgmgr option format: %s"
              (String.concat ":" parts))
  in let multi (parts : string list) =
    match parts with
    | [dist; pkgmgr; opts] -> ((dist, pkgmgr), parse_opts opts)
    | _ -> failwith (Printf.sprintf "invalid pkgmgr option format: %s"
              (String.concat ":" parts))
  in parse_info_file single multi

let parse_files_file =
  let single (parts : string list) =
    match parts with
    | [] | [""] -> All (StringSet.empty, StringSet.empty)
    | [pos; neg] -> All (parse_opts pos, parse_opts neg)
    | [dist; sys; pos; neg] ->
        Specific [((dist, if sys = "remote" then true else false),
                   (parse_opts pos, parse_opts neg))]
    | _ -> failwith (Printf.sprintf "invalid file option format: %s"
              (String.concat ":" parts))
  in let multi (parts : string list) =
    match parts with
    | [dist; sys; pos; neg] ->
        ((dist, if sys = "remote" then true else false),
         (parse_opts pos, parse_opts neg))
    | _ -> failwith (Printf.sprintf "invalid file option format: %s"
              (String.concat ":" parts))
  in parse_info_file single multi

let interp p =
  Interp.interpret p Interp.init_interp_state Calc.VariableMap.empty
    (* continue -- should not continue, should always return *)
    (fun _ _ -> Err "Ansible program reached end without return")
    (* yield -- nothing to yield to *)
    (fun _ _ _ -> Err "Ansible program yielded at top-level")
    (* return -- great! *)
    (fun s _ _ -> Success s)
    (* raise -- exception raised *)
    (fun _ _ (v, _) ->
      match v with
      | Literal (Except (_, exc, v), _) ->
          Err (Printf.sprintf "Exception %s(%s)" exc
            (Target.string_of_value v))
      | _ -> Err "Unknown Exception")

let validate_heuristics res : bool =
  begin
    if !users_src = "" then true
    else
      let user_info = parse_dist_file !users_src
      in match user_info with
      | All users ->
          Fql.Heuristics.valid_users users None res
      | Specific specs ->
          List.for_all (fun (dist, users) ->
            Fql.Heuristics.valid_users users (Some dist) res
          ) specs
  end
  &&
  begin
    if !groups_src = "" then true
    else
      let group_info = parse_dist_file !groups_src
      in match group_info with
      | All groups ->
          Fql.Heuristics.valid_groups groups None res
      | Specific specs ->
          List.for_all (fun (dist, groups) ->
            Fql.Heuristics.valid_groups groups (Some dist) res
          ) specs
  end
  &&
  begin
    if !packages_src = "" then true
    else
      let pkg_info = parse_pkgs_file !packages_src
      in match pkg_info with
      | All pkgs ->
          Fql.Heuristics.valid_packages pkgs None res
      | Specific specs ->
          List.for_all (fun (which, pkgs) ->
            Fql.Heuristics.valid_packages pkgs (Some which) res
          ) specs
  end
  &&
  begin
    if !files_src = "" then true
    else
      let files_info = parse_files_file !files_src
      in match files_info with
      | All (pos, neg) ->
        Fql.Heuristics.valid_files pos neg false None res
      | Specific specs ->
          List.for_all (fun (where, (pos, neg)) ->
            Fql.Heuristics.valid_files pos neg false (Some where) res
          ) specs
  end
  &&
  begin
    if !strict_files = "" then true
    else
      let files_info = parse_files_file !strict_files
      in match files_info with
      | All (pos, neg) ->
        Fql.Heuristics.valid_files pos neg true None res
      | Specific specs ->
          List.for_all (fun (where, (pos, neg)) ->
            Fql.Heuristics.valid_files pos neg true (Some where) res
          ) specs
  end
  &&
  begin
    if !reboot_hosts = "" then true
    else Fql.Heuristics.valid_reboot !reboot_hosts res
  end
  &&
  begin
    if !write_hosts = "" then true
    else Fql.Heuristics.valid_writes !write_hosts res
  end

let () = Printf.printf "\n";
  Arg.parse arglist anon_fun usage_msg;
  let parsed =
    match Modules.Parser.parse_files !module_defs with
    | Error msg ->
        Printf.printf "ERROR: While parsing module definitions, encountered\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let ctx =
    match Modules.Codegen.codegen parsed with
    | Error msg ->
        Printf.printf "ERROR: While lowering module definitions, encountered\n%s\n" msg
        ; exit 2
    | Ok ctx -> ctx

  in let query =
    let parsed =
      let ch = open_in !query
      in let s = really_input_string ch (in_channel_length ch)
      in let () = close_in ch
      in let lexbuf = Lexing.from_string s
      in Fql.Parser.query Fql.Lexer.token lexbuf
    in let stmt =
      Result.bind (Semant.analyze_top parsed) (fun query ->
        Result.bind (Fql.Codegen.codegen_query query) (fun query ->
          Modules.Codegen.codegen_program query ctx))
    in match stmt with
    | Error msg ->
        Printf.printf "ERROR: While lowering query, encountered\n%s\n" msg
        ; exit 3
    | Ok stmt -> stmt

  in let ansible =
    let stmt =
      Result.bind (Ansible.Parser.parse_ansible !program) (fun prg ->
        Result.bind (Ansible.Semant.process_playbook prg ctx) (fun typed ->
          Ansible.Codegen.codegen_playbook typed ctx))
    in match stmt with
    | Error msg ->
        Printf.printf "ERROR: While lowering Ansible, encountered\n%s\n" msg
        ; exit 4
    | Ok stmt -> stmt

  in let query_interp = interp query
  in let ansible_interp = interp ansible

  in let res = Fql.Verifier.unify_candidate query_interp ansible_interp
  in let merged = Fql.Verifier.merge_interp_res_unifier res

  in match merged with
  | Failed -> Printf.printf "FAILED TO VERIFY\n"; exit 5
  | Trivial -> Printf.printf "QUERY WAS TRIVIAL\n"; exit 6
  | Success m ->
      if validate_heuristics m
      then 
        let () = Printf.printf "VERIFIED\n"
        in let rec print_res (r : Fql.Verifier.merged_res) : unit =
          match r with
          | Both (x, y) | Either (x, y) ->
              print_res x; print_string "\n"; print_res y
          | Satisfied { base; diff } ->
              Ocolor_format.printf "@{<cyan>%s@} @{<yellow>{ %d branch }@} @{<red>assuming@} @{<orange>%s@} @{<red>and@} @{<orange>%s@} @{<red>performing@} @{<green>%s@}"
                (Modules.Target.string_of_state base)
                diff.branches
                (Fql.Verifier.string_of_merged_diff diff.inits)
                (Fql.Verifier.string_of_unifier_merged diff.constraints)
                (Fql.Verifier.string_of_merged_diff diff.finals)
        in let () = print_res m
        in print_string "\n"; exit 0
      else print_string "HEURISTICS REJECTED\n"; exit 7
