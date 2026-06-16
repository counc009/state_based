let usage_msg = "runner <ansible program> -- <module definitions>"
let program = ref ""
let module_defs = ref []

let anon_fun filename = program := filename

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definition")]

module Interp = Modules.Target.TargetInterp
module Calc   = Modules.Target.Ast_Target
module Target = Modules.Target

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
  in let prg = 
    match Ansible.Parser.parse_ansible !program with
    | Error msg ->
        Printf.printf "ERROR: While parsing Ansible code, encountered\n%s\n" msg
        ; exit 3
    | Ok prg -> prg
  in let typed =
    match Ansible.Semant.process_playbook prg ctx with
    | Error msg ->
        Printf.printf "ERROR: While processing Ansible code, encountered\n%s\n" msg
        ; exit 4
    | Ok typed -> typed
  in let stmt =
    match Ansible.Codegen.codegen_playbook typed ctx with
    | Error msg ->
        Printf.printf "ERROR: While lowering Ansible code, encountered\n%s\n" msg
        ; exit 5
    | Ok stmt -> stmt
  in let res =
    Interp.interpret stmt Interp.init_interp_state Calc.VariableMap.empty
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
  in match Target.string_of_res res with
  | Error msg ->
      Printf.printf "ERROR: While interpreting Ansible code, all branches failed\n%s\n" msg
      ; exit 6
  | Ok res ->
      Printf.printf "SUCCESS: Possible behaviours\n%s\n" res
