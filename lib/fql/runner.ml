let parse_query query =
  let lexbuf = Lexing.from_string query
  in let result = Parser.query Lexer.token lexbuf
  in result

module Semant = Semant.Semant(Knowledge.Example)

let analyze_query query = Semant.analyze_top (parse_query query)

let codegen_query query = Result.bind (analyze_query query) Codegen.codegen_query

let interp_query sources query =
  Result.bind (Modules.Parser.parse_files sources) (fun parsed ->
    let (types, env) = Modules.Codegen.codegen parsed
    in Result.bind (codegen_query query) (fun prg ->
      let prg = Modules.Codegen.codegen_program prg types env
      in let res = Modules.Target.TargetInterp.interpret prg (Primitive Unit)
      in Modules.Target.results_to_string res))
