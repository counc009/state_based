let parse_query query =
  let lexbuf = Lexing.from_string query
  in let result = Parser.query Lexer.token lexbuf
  in result

module Semant = Semant.Semant(Knowledge.Example)

let analyze_query query = Semant.analyze_top query
