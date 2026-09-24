let parse_string s =
  let lexbuf = Lexing.from_string s
  in Parser.program Lexer.token lexbuf

let parse_channel c =
  let lexbuf = Lexing.from_channel c
  in Parser.program Lexer.token lexbuf

let parse_file f =
  let lexbuf = Lexing.from_channel (open_in f)
  in Lexing.set_filename lexbuf f; Parser.program Lexer.token lexbuf

let rec print_semant_errors (errs : Semant.err_msg) : unit =
  match errs with
  | Leaf { pos = (x, y); msg } ->
      Printf.printf "%s (%d,%d -- %d,%d) error : %s\n"
        x.pos_fname
        x.pos_lnum (x.pos_cnum - x.pos_bol + 1)
        y.pos_lnum (y.pos_cnum - y.pos_bol)
        msg
  | Node (x, y) -> print_semant_errors x; print_semant_errors y
