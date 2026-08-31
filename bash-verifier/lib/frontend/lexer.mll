{
  open Lexing
  open Parser
  open Stdint

  let next_line lexbuf = new_line lexbuf

  exception LexerError of string
}

let digit = ['0'-'9']
let bin_digit = ['0'-'1']
let oct_digit = ['0'-'7']
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha = ['a'-'z' 'A'-'Z']

let ident    = (alpha) (alpha|digit|'_')*
let floating = digit+ '.' digit+ (['e' 'E'] ['+' '-']? digit+)?
let decimal  = digit+
let binary   = "0b" bin_digit+
let octal    = "0o" oct_digit+
let hex      = "0x" hex_digit+

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
  | "::<" { FISHTAIL }
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
  | "as"            { AS }
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
  | "struct"	      { STRUCT }
  | "then"	        { THEN }
  | "touch"	        { TOUCH }
  | "try"	          { TRY }
  | "type"	        { TYPE }
  | "uninterpreted"	{ UNINTERPRETED }
  | "yield"	        { YIELD }

  | "void"	  { VOID }
  | "bool"	  { BOOL }
  | "i8"	    { INT8 }
  | "i16"	    { INT16 }
  | "i32"	    { INT32 }
  | "i64"	    { INT64 }
  | "int"     { INT64 }
  | "u8"	    { UINT8 }
  | "u16"	    { UINT16 }
  | "u32"	    { UINT32 }
  | "u64"	    { UINT64 }
  | "f32"     { FLOAT32 }
  | "f64"     { FLOAT64 }
  | "string"  { STRING }
  | "state"   { STATE }
  | "list"    { LIST }

  | "true"  { BOOLLIT true }
  | "false" { BOOLLIT false }

  | decimal "i8"    { INT8LIT (Int8.of_string (lexeme lexbuf)) }
  | decimal "i16"   { INT16LIT (Int16.of_string (lexeme lexbuf)) }
  | decimal "i32"   { INT32LIT (Int32.of_string (lexeme lexbuf)) }
  | decimal "i64"   { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | decimal "u8"    { UINT8LIT (Uint8.of_string (lexeme lexbuf)) }
  | decimal "u16"   { UINT16LIT (Uint16.of_string (lexeme lexbuf)) }
  | decimal "u32"   { UINT32LIT (Uint32.of_string (lexeme lexbuf)) }
  | decimal "u64"   { UINT64LIT (Uint64.of_string (lexeme lexbuf)) }
  | binary "i8"     { INT8LIT (Int8.of_string (lexeme lexbuf)) }
  | binary "i16"    { INT16LIT (Int16.of_string (lexeme lexbuf)) }
  | binary "i32"    { INT32LIT (Int32.of_string (lexeme lexbuf)) }
  | binary "i64"    { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | binary "u8"     { UINT8LIT (Uint8.of_string (lexeme lexbuf)) }
  | binary "u16"    { UINT16LIT (Uint16.of_string (lexeme lexbuf)) }
  | binary "u32"    { UINT32LIT (Uint32.of_string (lexeme lexbuf)) }
  | binary "u64"    { UINT64LIT (Uint64.of_string (lexeme lexbuf)) }
  | octal "i8"      { INT8LIT (Int8.of_string (lexeme lexbuf)) }
  | octal "i16"     { INT16LIT (Int16.of_string (lexeme lexbuf)) }
  | octal "i32"     { INT32LIT (Int32.of_string (lexeme lexbuf)) }
  | octal "i64"     { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | octal "u8"      { UINT8LIT (Uint8.of_string (lexeme lexbuf)) }
  | octal "u16"     { UINT16LIT (Uint16.of_string (lexeme lexbuf)) }
  | octal "u32"     { UINT32LIT (Uint32.of_string (lexeme lexbuf)) }
  | octal "u64"     { UINT64LIT (Uint64.of_string (lexeme lexbuf)) }
  | hex "i8"        { INT8LIT (Int8.of_string (lexeme lexbuf)) }
  | hex "i16"       { INT16LIT (Int16.of_string (lexeme lexbuf)) }
  | hex "i32"       { INT32LIT (Int32.of_string (lexeme lexbuf)) }
  | hex "i64"       { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | hex "u8"        { UINT8LIT (Uint8.of_string (lexeme lexbuf)) }
  | hex "u16"       { UINT16LIT (Uint16.of_string (lexeme lexbuf)) }
  | hex "u32"       { UINT32LIT (Uint32.of_string (lexeme lexbuf)) }
  | hex "u64"       { UINT64LIT (Uint64.of_string (lexeme lexbuf)) }

  (* Just plain decimal becomes an INTLIT which is also used for tuple field
   * accesses (and is otherwise promoted to i64) *)
  | decimal         { INTLIT (int_of_string (lexeme lexbuf)) }
  | binary          { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | octal           { INT64LIT (Int64.of_string (lexeme lexbuf)) }
  | hex             { INT64LIT (Int64.of_string (lexeme lexbuf)) }

  | floating "f32"  { FLOAT32LIT (F32.of_float (float_of_string (lexeme lexbuf))) }
  | floating "f64"  { FLOAT64LIT (float_of_string (lexeme lexbuf)) }
  | floating        { FLOAT64LIT (float_of_string (lexeme lexbuf)) }
  | "'" _ "'" { CHARLIT (String.get (lexeme lexbuf) 1) }
  | '"' ([^'\n''\r''"''\\'] | '\\' _)* '"'
    { let l = lexeme lexbuf
      in STRINGLIT (String.sub l 1 (String.length l - 2)) }
  | ident     { ID (lexeme lexbuf) }
  | "_"       { UNDERSCORE }

  | "//"        { line_comment lexbuf }
  | "/*"        { block_comment (lexeme_start_p lexbuf) lexbuf; token lexbuf }
  | whitespace  { token lexbuf }
  | newline     { next_line lexbuf; token lexbuf }
  | eof         { EOF }
  | _           {
    let pos = lexeme_start_p lexbuf
    in let s = lexeme lexbuf
    in let msg =
      Printf.sprintf "Lexer error at line %d, column %d : invalid symbol '%s'"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) s
    in raise (LexerError msg) }

and line_comment = parse
  | newline { next_line lexbuf; token lexbuf }
  | eof     { EOF }
  | _       { line_comment lexbuf }

and block_comment start = parse
  | newline { next_line lexbuf; block_comment start lexbuf }
  | eof     {
    let msg =
      Printf.sprintf "Lexer error, comment at line %d, column %d not terminated"
        start.pos_lnum (start.pos_cnum - start.pos_bol + 1)
    in raise (LexerError msg) }
  | "*/"    { () }
  | "/*"    {
    let p = lexeme_start_p lexbuf
    in block_comment p lexbuf; block_comment start lexbuf }
  | _       { block_comment start lexbuf }
