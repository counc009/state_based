module Interp = Modules.Target.TargetInterp
module Calc   = Modules.Target.Ast_Target
module Target = Modules.Target

let () =
  let print_interp res =
    match Modules.Target.string_of_res res with
    | Error msg -> Printf.printf "ERROR\n%s\n\n" msg
    | Ok msg -> Printf.printf "SUCCESS\n%s\n\n" msg

  in let verify f =
    let parsed =
      match Modules.Parser.parse_file ("arduino/" ^ f) with
      | Error msg ->
          Printf.printf "ERROR: While processing definition, encounterd\n%s\n" msg
          ; exit 1
      | Ok parsed -> parsed
    in let ctx =
      match Modules.Codegen.codegen [parsed] with
      | Error msg ->
          Printf.printf "ERROR: While lowering definition, encountered\n%s\n" msg
          ; exit 2
      | Ok ctx -> ctx

    in let interp_prg p =
      Interp.interpret p Interp.init_interp_state Calc.VariableMap.empty
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
      let parsed = Modules.Parser.parse_stmts_string {| query(); |}
      in match Modules.Codegen.codegen_program parsed ctx with
      | Error msg ->
          Printf.printf "ERROR: While lowering query, encountered\n%s\n" msg
          ; exit 3
      | Ok query -> query
    in let impl_prg =
      let parsed = Modules.Parser.parse_stmts_string {| program(); |}
      in match Modules.Codegen.codegen_program parsed ctx with
      | Error msg ->
          Printf.printf "ERROR: While lowering impl, encountered\n%s\n" msg
          ; exit 4
      | Ok query -> query

    in let query_res = interp_prg query_prg
    in let impl_res = interp_prg impl_prg

    in let _ = print_interp query_res
    in let _ = print_interp impl_res

    in match Fql.Verifier.unify_candidate query_res impl_res with
    | Some _ -> Printf.printf "VERIFIED\n"
    | None -> Printf.printf "FAILED TO VERIFY\n"; exit 5

  in verify "toggle_polling.calc"
