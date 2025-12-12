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
  in let interpret_prg p =
    let prg = Modules.Codegen.codegen_program p types env
    in Modules.Target.TargetInterp.interpret prg (Primitive Unit)

  in let query_prg =
    Modules.Parser.parse_stmts_string {|
      assert exists env();
      fql();
    |}
  in let fun_prg =
    Modules.Parser.parse_stmts_string {|
      assert exists env();
      assert env().time_counter == 0;
      fd(0).kind = fd::stdin;
      fd(1).kind = fd::stdout;
      fd(2).kind = fd::stderr;
      fun_one();
    |}
  in let normal_prg =
    Modules.Parser.parse_stmts_string {|
      assert exists env();
      assert env().time_counter == 0;
      fd(0).kind = fd::stdin;
      fd(1).kind = fd::stdout;
      fd(2).kind = fd::stderr;
      normal_one();
    |}
  in let cat_prg =
    Modules.Parser.parse_stmts_string {|
      assert exists env();
      assert env().time_counter == 0;
      fd(0).kind = fd::stdin;
      fd(1).kind = fd::stdout;
      fd(2).kind = fd::stderr;
      cat_one();
    |}

  in let query_res = interpret_prg query_prg
  in let fun_res = interpret_prg fun_prg
  in let normal_res = interpret_prg normal_prg
  in let cat_res = interpret_prg cat_prg

  in let res_fun = Fql.Verifier.verify query_res fun_res
  in let res_normal = Fql.Verifier.verify query_res normal_res
  in let res_cat = Fql.Verifier.verify query_res cat_res

  in Printf.printf "Fun Script Result\n"
   ; let _ = Fql.Verifier.print_verification res_fun
  in Printf.printf "\n\nNormal Script Result\n"
   ; let _ = Fql.Verifier.print_verification res_normal
  in Printf.printf "\n\nCat Script Result\n"
   ; let _ = Fql.Verifier.print_verification res_cat
  in ()
