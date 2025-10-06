let () =
  let files = List.filter_map
                (fun x -> if Filename.extension x = ".util"
                          then Some ("bash/" ^ x)
                          else None)
                (Array.to_list (Sys.readdir "bash"))
  in let parsed =
    match Modules.Parser.parse_files files with
    | Error msg ->
        Printf.printf "ERROR: While processing utility definitions, encounterd\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let (types, env) = Modules.Codegen.codegen parsed
  in let prg =
    Modules.Parser.parse_stmts_string {|
      assert exists env();
      assert env().time_counter == 0;
      fd(0).kind = fd::stdin;
      fd(1).kind = fd::stdout;
      fd(2).kind = fd::stderr;
      normal_one();
    |}
  in let prg = Modules.Codegen.codegen_program prg types env
  in let res = Modules.Target.TargetInterp.interpret prg (Primitive Unit)
  in match Modules.Target.results_to_string res with
  | Error msg ->
      Printf.printf "ERROR: While interpreting fun one, all branches failed\n%s\n" msg
      ; exit 3
  | Ok res ->
      Printf.printf "SUCCESS: Possible behaviours\n%s\n" res
