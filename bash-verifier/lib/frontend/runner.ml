let parse_string s =
  let lexbuf = Lexing.from_string s
  in Parser.program Lexer.token lexbuf

let parse_channel c =
  let lexbuf = Lexing.from_channel c
  in Parser.program Lexer.token lexbuf

let parse_file f = parse_channel (open_in f)
