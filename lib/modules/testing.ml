module Interp = Target.TargetInterp
module Calc = Target.Ast_Target

let ( let^ ) r f = Result.bind r f

let test (p : string) =
  let^ parsed = Parser.parse_files ["../../examples/examples.mdl"]
  in let^ context = Codegen.codegen parsed
  in let^ s = Codegen.codegen_program (Parser.parse_stmts_string p) context
  in let b =
    Interp.interpret s Interp.init_interp_state Calc.VariableMap.empty
      (* continue -- should not continune, should always return [for now] *)
      (fun _ _ -> Err "Program reached end without return")
      (* yield -- nothing to yield to *)
      (fun _ _ _ -> Err "Program yielded at top-level")
      (* return -- great! *)
      (fun s _ _ -> Success s)
      (* raise -- exception raised *)
      (fun _ _ (v, _) ->
        match v with
        | Pair (Literal (String exc, _), v, _) ->
            Err (Printf.sprintf "Exception (%s) : %s" exc 
                  (Target.string_of_value v))
        | _ -> Err "Unknown Exception")
  in match Target.string_of_res b with
  | Error msg -> Ok (Printf.printf "\nInterpretation Failed:\n%s\n\n" msg)
  | Ok msg -> Ok (Printf.printf "\nInterpretation Succeeded:\n%s\n\n" msg)

let debug_global (nm : string) =
  let nm = String.split_on_char '.' nm
  in let^ parsed = Parser.parse_files ["../../examples/examples.mdl"]
  in let^ context = Codegen.codegen parsed
  in let^ body = Codegen.find_function_body nm context
  in Ok (Printf.printf "\n\n%s\n\n" (Target.string_of_stmt body))
