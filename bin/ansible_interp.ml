let usage_msg = "runner <ansible program> -- <module definitions>"
let program = ref ""
let module_defs = ref []

let anon_fun filename = program := filename

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definition")]

let () = Printf.printf "\n";
  Arg.parse arglist anon_fun usage_msg;
  let parsed =
    match Modules.Parser.parse_files !module_defs with
    | Error msg ->
        Printf.printf "ERROR: While processing module definitions, encountered\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let (types, env) = Modules.Codegen.codegen parsed
  in let prg = 
    match Ansible.Parser.process_ansible !program types env with
    | Error msg ->
        Printf.printf "ERROR: While processing Ansible code, encountered\n%s\n" msg
        ; exit 2
    | Ok prg -> prg
  in let prg = Modules.Codegen.codegen_program prg types env
  in let res = Modules.Target.TargetInterp.interpret prg (Primitive Unit)
  in match Modules.Target.results_to_string res with
  | Error msg ->
      Printf.printf "ERROR: While interpreting Ansible code, all branches failed\n%s\n" msg
      ; exit 3
  | Ok res ->
      Printf.printf "SUCCESS: Possible behaviours\n%s\n" res
