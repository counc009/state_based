let () =
  let print_interp res =
    match Modules.Target.results_to_string res with
    | Error msg -> Printf.printf "ERROR\n%s\n\n" msg
    | Ok msg -> Printf.printf "SUCCESS\n%s\n\n" msg

  in let verify f =
    let parsed =
      match Modules.Parser.parse_file ("arduino/" ^ f) with
      | Error msg ->
          Printf.printf "ERROR: While processing definition, encounterd\n%s\n" msg
          ; exit 1
      | Ok parsed -> parsed
    in let (types, env) = Modules.Codegen.codegen [parsed]

    in let interp_prg p =
      let prg = Modules.Codegen.codegen_program p types env
      in Modules.Target.TargetInterp.interpret prg (Primitive Unit)

    in let query_prg = Modules.Parser.parse_stmts_string {| query(); |}
    in let refer_prg = Modules.Parser.parse_stmts_string {| program(); |}

    in let query_res = interp_prg query_prg
    in let refer_res = interp_prg refer_prg

    in let _ = print_interp query_res
    in let _ = print_interp refer_res

    in Fql.Verifier.verify query_res refer_res

  in let _ = Fql.Verifier.print_verification (verify "toggle_polling.calc")
  in ()
