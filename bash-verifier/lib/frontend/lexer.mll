{
  open Lexing
  open Parser

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with pos_bol  = lexbuf.lex_curr_pos;
                                    pos_lnum = pos.pos_lnum + 1 }
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']

let integer = '-'? digit+
let ident   = (alpha) (alpha|digit|'_')*

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule token = parse
  | "("   { LPAREN }
  | ")"   { RPAREN }
  | "{"   { LCURLY }
  | "}"   { RCURLY }
  | ","   { COMMA }
  | "."   { DOT }
  | ";"   { SEMICOLON }
  | "::"  { COLONCOLON }
  | ":"   { COLON }
  | "->"  { SINGLEARROW }
  | "=>"  { DOUBLEARROW }
  | "*"   { MUL }
  | "/"   { DIV }
  | "%"   { MOD }
  | "+"   { ADD }
  | "-"   { SUB }
  | "<<"  { LSHIFT }
  | ">>"  { RSHIFT }
  | "<="  { LE }
  | "<"   { LT }
  | ">="  { GE }
  | ">"   { GT }
  | "="   { ASSIGN }
  | "=="  { EQ }
  | "!="  { NE }
  | "&&"  { LOGAND }
  | "&"   { BITAND }
  | "||"  { LOGOR }
  | "|"   { BITOR }
  | "^"   { BITXOR }
  | "~"   { BITNOT }
  | "!"   { LOGNOT }

  | "assert"	      { ASSERT }
  | "attribute"	    { ATTRIBUTE }
  | "catch"	        { CATCH }
  | "clear"	        { CLEAR }
  | "element"	      { ELEMENT }
  | "else"	        { ELSE }
  | "enum"	        { ENUM }
  | "exception"	    { EXCEPTION }
  | "exists"	      { EXISTS }
  | "finally"	      { FINALLY }
  | "fn"	          { FN }
  | "for"	          { FOR }
  | "if"	          { IF }
  | "in"	          { IN }
  | "let"	          { LET }
  | "localize"	    { LOCALIZE }
  | "local"         { LOCAL }
  | "match"	        { MATCH }
  | "raise"	        { RAISE }
  | "return"	      { RETURN }
  | "sizeof"	      { SIZEOF }
  | "struct"	      { STRUCT }
  | "then"	        { THEN }
  | "touch"	        { TOUCH }
  | "try"	          { TRY }
  | "type"	        { TYPE }
  | "uninterpreted"	{ UNINTERPRETED }
  | "union"         { UNION }
  | "yield"	        { YIELD }

  | "void"	  { VOID }
  | "bool"	  { BOOL }
  | "int8"	  { INT8 }
  | "int16"	  { INT16 }
  | "int32"	  { INT32 }
  | "int64"	  { INT64 }
  | "uint8"	  { UINT8 }
  | "uint16"	{ UINT16 }
  | "uint32"	{ UINT32 }
  | "uint64"	{ UINT64 }
  | "float32" { FLOAT32 }
  | "float64" { FLOAT64 }
  | "array"   { ARRAY }
  | "ptr"     { PTR }
  | "state"   { STATE }

  (* TODO *)
  (* Int Literals: https://en.cppreference.com/cpp/language/integer_literal *)
  (* Float Literals: https://en.cppreference.com/cpp/language/floating_literal *)
  (* String Literals: https://en.cppreference.com/c/language/string_literal *)
  | "true"    { BOOLLIT true }
  | "false"   { BOOLLIT false }
  | "'" _ "'" { CHARLIT (String.get (lexeme lexbuf) 1) }
  | ident     { ID (lexeme lexbuf) }

  | "//"        { line_comment lexbuf }
  | "/*"        { block_comment lexbuf; token lexbuf }
  | whitespace  { token lexbuf }
  | newline     { next_line lexbuf; token lexbuf }
  | eof         { EOF }
  | _           { failwith "TODO: fail?" }

and line_comment = parse
  | newline { next_line lexbuf; token lexbuf }
  | eof     { EOF }
  | _       { line_comment lexbuf }

and block_comment = parse
  | newline { next_line lexbuf; block_comment lexbuf }
  | eof     { failwith "TODO: fail?" }
  | "*/"    { () }
  | "/*"    { block_comment lexbuf; block_comment lexbuf }
  | _       { block_comment lexbuf }
