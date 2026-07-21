let usage_msg = "runner <query> -- <module definitions>"
let query = ref ""
let module_defs = ref []

let anon_fun filename = query := filename

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definition")]

module Interp = Modules.Target.TargetInterp
module Calc = Modules.Target.Ast_Target
module Target = Modules.Target

module Semant = Fql.Semant.Semant(Fql.Knowledge.Example)

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
  in let query_parsed =
    let ch = open_in !query
    in let s = really_input_string ch (in_channel_length ch)
    in let () = close_in ch
    in let lexbuf = Lexing.from_string s
    in Fql.Parser.query Fql.Lexer.token lexbuf
  in let query =
    let query =
      Result.bind (Semant.analyze_top query_parsed) (fun query ->
        Result.bind (Fql.Codegen.codegen_query query) (fun query ->
          Modules.Codegen.codegen_program query ctx))
    in match query with
    | Error msg ->
        Printf.printf "ERROR: While lowering query, encountered\n%s\n" msg
        ; exit 4
    | Ok query -> query
  in let res =
    Interp.interpret query Interp.init_interp_state Calc.VariableMap.empty
      (* continue -- should not continue, should always return *)
      (fun _ _ -> Err "FQL program reached end without return")
      (* yield -- nothing to yield to *)
      (fun _ _ _ -> Err "FQL program yielded at top-level")
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
      Printf.printf "ERROR: While interpreting query, all branches failed\n%s\n" msg
      ; exit 5
  | Ok res ->
      Printf.printf "SUCCESS: Possible behaviors\n%s\n" res
