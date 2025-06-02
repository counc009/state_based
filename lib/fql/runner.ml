let parse_query query =
  let lexbuf = Lexing.from_string query
  in let result = Parser.query Lexer.token lexbuf
  in result
