let usage_msg = "runner <query> -- <module definitions>"
let query = ref ""
let module_defs = ref []

let anon_fun filename = query := filename

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definition")]

let () =
  Arg.parse arglist anon_fun usage_msg;
  let parsed =
    match Modules.Parser.parse_files !module_defs with
    | Error msg ->
        Printf.printf "ERROR: While processing module definitions, encountered\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let (types, env) = Modules.Codegen.codegen parsed
  in let prg =
    let ch = open_in !query
    in let s = really_input_string ch (in_channel_length ch)
    in let () = close_in ch
    in Fql.Runner.codegen_query s
  in match prg with
  | Error msg -> Printf.printf "ERROR in query: %s\n" msg; exit 1
  | Ok prg ->
      let prg = Modules.Codegen.codegen_program prg types env
      in let res = Modules.Target.TargetInterp.interpret prg (Primitive Unit)
      in match Modules.Target.results_to_string res with
      | Error msg ->
          Printf.printf "ALL BRANCHES FAILED\n%s\n" msg; exit 2
      | Ok res -> Printf.printf "SUCCESS\n%s\n" res
