module Interp = Modules.Target.TargetInterp
module Calc   = Modules.Target.Ast_Target
module Target = Modules.Target

let verify ref cand = Fql.Verifier.unify_candidate ref cand

let print_verification res =
  match res with
  | Some _ -> Printf.printf "VERIFIED\n"
  | None -> Printf.printf "FAILED TO VERIFY\n"

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
  in let ctx =
    match Modules.Codegen.codegen parsed with
    | Error msg ->
        Printf.printf "ERROR: While lowering utility definitions, encountered\n%s\n" msg
        ; exit 2
    | Ok ctx -> ctx

  in let interpret_prg p =
    let prg =
      match Modules.Codegen.codegen_program p ctx with
      | Error msg ->
          Printf.printf "ERROR: While lowering program, encountered\n%s\n" msg
          ; exit 3
      | Ok prg -> prg
    in Interp.interpret prg Interp.init_interp_state Calc.VariableMap.empty
      (* continue -- should not continue, should always return *)
      (fun _ _ -> Err "Program reached end without return")
      (* yield -- nothing to yield to *)
      (fun _ _ _ -> Err "Program yielded at top-level")
      (* return -- great! *)
      (fun s _ _ -> Success s)
      (* raise -- exception raised *)
      (fun _ _ (v, _) ->
        match v with
        | Literal (Except (_, exc, v), _) ->
            Err (Printf.sprintf "Exception %s(%s)" exc
              (Target.string_of_value v))
        | _ -> Err "Unknown Exception")

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

  in let res_fun = verify query_res fun_res
  in let res_normal = verify query_res normal_res
  in let res_cat = verify query_res cat_res

  in Printf.printf "Fun Script Result\n"
   ; let _ = print_verification res_fun
  in Printf.printf "\n\nNormal Script Result\n"
   ; let _ = print_verification res_normal
  in Printf.printf "\n\nCat Script Result\n"
   ; let _ = print_verification res_cat
  in ()
