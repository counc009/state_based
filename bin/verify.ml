let usage_msg = "runner <query> <ansible program> -- <module definitions>"
let query = ref ""
let program = ref ""
let module_defs = ref []

let cnt = ref 0
let anon_fun filename =
  (if !cnt = 0 then query := filename
  else if !cnt = 1 then program := filename
  else failwith "Only expected two anonymous arguments"); cnt := !cnt + 1

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definitions")]

let () = Printf.printf "\n";
  Arg.parse arglist anon_fun usage_msg;
  let parsed =
    match Modules.Parser.parse_files !module_defs with
    | Error msg ->
        Printf.printf "ERROR: While processing module definitions, encountered\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let (types, env) = Modules.Codegen.codegen parsed
  in let interpret_prg p =
    let prg = Modules.Codegen.codegen_program p types env
    in Modules.Target.TargetInterp.interpret prg (Primitive Unit)

  in let query_prg =
    let ch = open_in !query
    in let s = really_input_string ch (in_channel_length ch)
    in let () = close_in ch
    in Fql.Runner.codegen_query s
  in let ansible_prg = Ansible.Parser.process_ansible !program types env

  in let query_interp = Result.map interpret_prg query_prg
  in let ansible_interp = Result.map interpret_prg ansible_prg

  in let query_res = match query_interp with Ok i -> i
                     | Error msg -> Printf.printf "ERROR in query: %s\n" msg
                                  ; exit 2
  in let ansible_res = match ansible_interp with Ok i -> i
                     | Error msg -> Printf.printf "ERROR in ansible: %s\n" msg
                                  ; exit 2

  in let res = Fql.Verifier.verify query_res ansible_res
  in Fql.Verifier.print_verification res
