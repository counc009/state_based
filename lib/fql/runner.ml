let parse_query query =
  let lexbuf = Lexing.from_string query
  in let result = Parser.query Lexer.token lexbuf
  in result

module Semant = Semant.Semant(Knowledge.Example)

let analyze_query query = Semant.analyze_top (parse_query query)

let codegen_query query = Result.bind (analyze_query query) Codegen.codegen_query

module Interp = Modules.Target.TargetInterp
module Calc = Modules.Target.Ast_Target
module Target = Modules.Target

let interp_query_string sources query =
  let interp p : Interp.interp_res =
    Interp.interpret p Interp.init_interp_state Calc.VariableMap.empty
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
  in Result.bind (Modules.Parser.parse_files sources) (fun parsed ->
      Result.bind (Modules.Codegen.codegen parsed) (fun ctx ->
        Result.bind (codegen_query query) (fun prg ->
          Result.bind (Modules.Codegen.codegen_program prg ctx) (fun prg ->
            Ok (interp prg)))))

let interp_query sources file =
  let ch = open_in file
  in let s = really_input_string ch (in_channel_length ch)
  in close_in ch
  ; interp_query_string sources s
