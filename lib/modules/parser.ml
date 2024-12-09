open Angstrom
open Ast

let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _ -> false

let whitespace = take_while is_whitespace

let whitespace1 = take_while1 is_whitespace

let is_digit = function '0'..'9' -> true | _ -> false

let integer = take_while1 is_digit

let sign =
  peek_char
  >>= function
    | Some '-' -> advance 1 >>| fun () -> "-"
    | Some '+' -> advance 1 >>| fun () -> "+"
    | Some c when (is_digit c) ->  return "+"
    | _ -> fail "Sign or digit expected"

let dot =
  peek_char
  >>= function
    | Some '.' -> advance 1 >>| fun () -> true
    | _ -> return false

let identifier =
  satisfy (function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false)
  >>= fun c ->
  take_while (function 'a'..'z' | 'A'..'Z' | '_' | '-' | '0'..'9' -> true | _ -> false)
  >>| fun rest -> String.make 1 c ^ rest

let module_name = sep_by1 (char '.') identifier

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'
let brackets p = char '{' *> whitespace *> p <* whitespace <* char '}'
let square p = char '[' *> whitespace *> p <* whitespace <* char ']'
let doub_bracks p = string "{{" *> whitespace *> p <* whitespace <* string "}}"

let optional p =
  option None (lift (fun x -> Some x) p)

let typ =
  fix (fun t ->
    choice
      [ (string "bool"   >>| fun _ -> Bool)
      ; (string "int"    >>| fun _ -> Int)
      ; (string "float"  >>| fun _ -> Float)
      ; (string "string" >>| fun _ -> String)
      ; (string "path"   >>| fun _ -> Path)
      ; (string "list" *> whitespace1 *> t >>| fun t -> List t)
      ; (identifier >>| fun nm -> Named nm)
      ; (parens (sep_by (whitespace *> char ',' *> whitespace) t)
        >>| function
          | [] -> Unit
          | [t] -> t
          | ts -> Product ts)
      ])

(* Function arguments are of the form <name> : <type> *)
let func_arg =
  identifier
  >>= fun nm ->
  whitespace
  *> char ':'
  *> whitespace
  *> typ
  >>| fun typ -> (nm, typ)

let func_args =
  sep_by (whitespace *> char ',' *> whitespace) func_arg

let number =
  sign
  >>= fun sign ->
  take_while1 is_digit
  >>= fun whole ->
  dot
  >>= function
  | false -> return (IntLit (int_of_string (sign ^ whole)))
  | true ->
      take_while1 is_digit >>= fun part ->
        return (FloatLit (float_of_string (sign ^ whole ^ "." ^ part)))

let string_lit =
  let string_body =
    many ((take_while1 (function '\\' | '"' -> false | _ -> true))
          <|> (char '\\' *> any_char >>| fun c -> String.make 1 c))
    >>| String.concat ""
  in char '"'
  *> string_body
  <* char '"'

(* Parsing of expressions is similar to how we would parse a disambiguated
   CFG with precedence, so we use a number of auxiliary nonterminals. The CFG
   for this is roughly:
    expr  ::= expr1
    expr1 ::= expr1 '||' expr2 | expr2
    expr2 ::= expr2 '&&' expr3 | expr3
    expr3 ::= expr4 '==' expr4 | expr4 '!=' expr4
            | expr4 '<'  expr4 | expr4 '<=' expr4
            | expr4 '>'  expr4 | expr4 '>=' expr4
            | expr4
    expr4 ::= expr4 '<<' expr5 | expr4 '>>' expr5 | expr5
    expr5 ::= expr5 '+' expr6 | expr5 '-' expr6 | expr6
    expr6 ::= expr6 '*' expr7 | expr6 '/' expr7 | expr6 '%' expr7 | expr7
    expr7 ::= '!' expr7 | '-' expr7 | expr8
    expr8 ::= expr8 '.' identifier | expr8 '::' identifier ['(' exprs ')']
            | expr8 '(' exprs ')' | expr8 '{' fields '}'
            | expr8 '{{' fields '}}' | expr9
    expr9 ::= identifier | literals | '(' exprs ')'
   in the implementation we eliminate left recursion in the standard way
*)
let expr =
  fix (fun expr ->

    let exprs = sep_by (whitespace *> char ',' *> whitespace) expr
    in let field_expr =
      identifier <* whitespace <* char ':' <* whitespace
      >>= fun field -> expr >>| fun exp -> (field, exp)
    in let fields =
      sep_by (whitespace *> char ',' *> whitespace) field_expr

    in let expr9 =
      choice
      [ string "true"  *> return (BoolLit true)
      ; string "false" *> return (BoolLit false)
      ; number
      ; (string_lit >>| fun str -> StringLit str)
      ; (identifier >>| fun nm -> Id nm)
      ; (parens exprs >>| function [] -> UnitExp
                                 | [x] -> x
                                 | xs -> ProductExp xs)
      ]
    in let expr8 =
      let rec expr8' exp =
        whitespace
        *> choice
          [ (char '.' *> whitespace *>
            ((identifier >>= fun field -> expr8' (Field (exp, field)))
            <|> (take_while1 is_digit 
              >>= fun whole -> expr8' (ProductField (exp, int_of_string whole)))))
          ; (string "::" *> whitespace *>
              ((identifier >>= fun variant ->
                option [] (parens exprs)
                >>= fun args -> expr8' (EnumExp (exp, variant, args)))))
          ; (parens exprs >>= fun args -> expr8' (FuncExp (exp, args)))
          ; (doub_bracks fields >>= fun args -> expr8' (ModuleExp (exp, args)))
          ; (brackets fields >>= fun args -> expr8' (RecordExp (exp, args)))
          ; (return exp)
          ]
      in expr9 >>= expr8'
    in let expr7 =
      fix (fun expr7 ->
        choice
        [ (char '!' *> whitespace *> expr7 >>| fun exp -> UnaryExp (exp, Not))
        ; (char '-' *> whitespace *> expr7 >>| fun exp -> UnaryExp (exp, Neg))
        ; expr8
        ])
    in let expr6 =
      let rec expr6' lhs =
        whitespace
        *> option lhs
          (choice
          [ (char '*' *> whitespace *> expr7
              >>= fun rhs -> expr6' (BinaryExp (lhs, rhs, Mul)))
          ; (char '/' *> whitespace *> expr7
              >>= fun rhs -> expr6' (BinaryExp (lhs, rhs, Div)))
          ; (char '%' *> whitespace *> expr7
              >>= fun rhs -> expr6' (BinaryExp (lhs, rhs, Mod))) ])
      in expr7 >>= expr6'
    in let expr5 =
      let rec expr5' lhs =
        whitespace
        *> option lhs
          (choice
          [ (char '+' *> whitespace *> expr6
              >>= fun rhs -> expr5' (BinaryExp (lhs, rhs, Add)))
          ; (char '-' *> whitespace *> expr6
              >>= fun rhs -> expr5' (BinaryExp (lhs, rhs, Sub))) ])
      in expr6 >>= expr5'
    in let expr4 =
      let rec expr4' lhs =
        whitespace
        *> option lhs
          (choice
          [ (string "<<" *> whitespace *> expr5
              >>= fun rhs -> expr4' (BinaryExp (lhs, rhs, LShift)))
          ; (string ">>" *> whitespace *> expr5
              >>= fun rhs -> expr4' (BinaryExp (lhs, rhs, RShift))) ])
      in expr5 >>= expr4'
    in let expr3 =
      expr4
      >>= fun lhs ->
      whitespace
      *> choice
        [ (string "==" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Eq))
        ; (string "!=" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Ne))
        ; (string "<=" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Le))
        ; (string "<" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Lt))
        ; (string ">=" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Ge))
        ; (string ">" *> whitespace *> expr4
            >>| fun rhs -> BinaryExp (lhs, rhs, Gt))
        ; (return lhs)
        ]
    in let expr2 =
      let rec expr2' lhs =
        whitespace
        *> option lhs
          (string "&&" *> whitespace *> expr3
            >>= fun rhs -> expr2' (BinaryExp (lhs, rhs, And)))
      in expr3 >>= expr2'
    in let expr1 =
      let rec expr1' lhs =
        whitespace
        *> option lhs
          (string "||" *> whitespace *> expr2
            >>= fun rhs -> expr1' (BinaryExp (lhs, rhs, Or)))
      in expr2 >>= expr1'
    in expr1)

(* Module arguments are of the form <name> [aka <names>] : <type> [= <default>] *)
let mod_aka =
  option [] (string "aka" *> whitespace 
            *> sep_by1 (whitespace *> char ',' *> whitespace) identifier)

let mod_arg =
  identifier
  >>= fun nm ->
  whitespace
  *> mod_aka
  >>= fun alias ->
  whitespace
  *> char ':'
  *> whitespace
  *> typ
  >>= fun typ ->
  whitespace
  *> optional (char '=' *> whitespace *> expr)
  >>| fun default -> (nm, alias, typ, default)

(* Module arguments are separated by | since they represent options *)
let mod_args =
  sep_by (whitespace *> char '|' *> whitespace) mod_arg

(* A (match) pattern has form <name>[(<names>)] *)
let pattern =
  identifier
  >>= fun nm ->
  option []
    (whitespace
      *> parens (sep_by (whitespace *> char ',' *> whitespace) identifier))
  >>| fun vars -> (nm, vars)

type condType = Provided of string | Exists of expr | Condition of expr

let stmt =
  fix (fun stmt ->
    let stmts = sep_by whitespace stmt

    in let forLoop =
      string "for"
      *> whitespace1
      *> identifier
      >>= fun var ->
      whitespace1
      *> string "in"
      *> whitespace1
      *> expr
      >>= fun lst ->
      whitespace
      *> brackets stmts
      >>| fun body -> ForLoop (var, lst, body)

    in let elseStmt : stmt list t =
      fix (fun elseStmt ->
        option []
          (string "else" *>
            choice
            [ (whitespace1 *> string "if" *> whitespace1
                *> ((string "provided" *> whitespace1 *> identifier
                      >>| fun nm -> Provided nm)
                <|> (string "exists" *> whitespace1 *> expr
                      >>| fun ex -> Exists ex)
                <|> (expr >>| fun ex -> Condition ex))
              >>= fun cond ->
              whitespace *> brackets stmts
              >>= fun thn ->
              whitespace *> elseStmt
              >>| fun els ->
                match cond with
                | Provided nm    -> [IfProvided (nm, thn, els)]
                | Exists e       -> [IfExists (e, thn, els)]
                | Condition cond -> [IfThenElse (cond, thn, els)])
            ; (whitespace *> brackets stmts)
            ]))

    in let ifStmts =
      string "if"
      *> whitespace1
      *> ((string "provided" *> whitespace1 *> identifier
            >>| fun nm -> Provided nm)
          <|> (string "exists" *> whitespace1 *> expr
            >>| fun ex -> Exists ex)
          <|> (expr >>| fun ex -> Condition ex))
      >>= fun cond ->
      whitespace
      *> brackets stmts
      >>= fun thn ->
      whitespace *> elseStmt
      >>| fun els ->
        match cond with
        | Provided nm    -> IfProvided (nm, thn, els)
        | Exists e       -> IfExists (e, thn, els)
        | Condition cond -> IfThenElse (cond, thn, els)

    in let matchCase =
      pattern
      >>= fun pat ->
      whitespace
      *> string "=>"
      *> whitespace
      *> brackets stmts
      >>| fun body -> (pat, body)

    in let cases = whitespace *> sep_by whitespace matchCase

    in let matchStmt =
      string "match"
      *> whitespace1
      *> expr
      >>= fun ex ->
      whitespace
      *> brackets cases
      >>| fun cs -> Match (ex, cs)

    in let keywordStmt (keyword : string) (c : expr -> stmt) =
      string keyword *> whitespace1
      *> expr
      <* whitespace <* char ';'
      >>| c

    in let assignStmt =
      expr
      >>= fun lhs ->
      whitespace
      *> char '='
      *> whitespace
      *> expr
      <* whitespace
      <* char ';'
      >>| fun rhs -> Assign (lhs, rhs)

    in choice 
    [ (parens mod_args >>| fun args -> RequiredVar args)
    ; (square mod_args >>| fun args -> OptionalVar args)
    ; forLoop
    ; ifStmts
    ; matchStmt
    ; keywordStmt "clear"  (fun e -> Clear e)
    ; keywordStmt "assert" (fun e -> Assert e)
    ; keywordStmt "return" (fun e -> Return e)
    ; assignStmt
    ]
  )

let stmts = whitespace *> sep_by whitespace stmt

(* ptype parsed an already parens type, hence we handle commas *)
let ptype =
  sep_by (whitespace *> char ',' *> whitespace) typ
  >>| function
    | [] -> Unit
    | [t] -> t
    | ts -> Product ts

let types =
  sep_by (whitespace *> char ',' *> whitespace) typ

let enum_case =
  identifier
  >>= fun nm ->
  whitespace
  *>
  optional (parens types)
  >>| fun ty -> (nm, ty)

let enum_cases =
  sep_by (whitespace *> char ',' *> whitespace) enum_case

let enum_def =
  string "enum"
  *> whitespace
  *> identifier
  <* whitespace
  >>= fun nm ->
  brackets enum_cases
  >>| fun def -> Enum (nm, def)

let struct_field =
  identifier
  >>= fun nm ->
  whitespace
  *> char ':'
  *> whitespace
  *> typ
  >>| fun typ -> (nm, typ)

let struct_fields =
  sep_by (whitespace *> char ',' *> whitespace) struct_field

let struct_def =
  string "struct"
  *> whitespace
  *> identifier
  <* whitespace
  >>= fun nm ->
  brackets struct_fields
  >>| fun def -> Struct (nm, def)

let uninterp_def =
  string "uninterpreted"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens types
  >>= fun args ->
  whitespace
  *> string "->"
  *> whitespace
  *> typ
  >>| fun res -> Uninterp (nm, args, res)

let attr_def =
  string "attribute"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens ptype
  >>| fun t -> Attribute (nm, t)

let elem_def =
  string "element"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens ptype
  >>| fun t -> Element (nm, t)

let func_def =
  string "function"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens func_args
  >>= fun args ->
  whitespace
  *> optional (string "->" *> whitespace *> typ)
  >>= fun retTy ->
  whitespace
  *> brackets stmts
  >>| fun body -> Function (nm, args, retTy, body)

let mod_def =
  string "module"
  *> whitespace
  *> module_name
  >>= fun nm ->
  whitespace
  *> optional (string "->" *> whitespace *> typ)
  >>= fun retTy ->
  whitespace
  *> brackets stmts
  >>| fun body -> Module (nm, retTy, body)

let top_level =
  sep_by whitespace
    (choice
      [ enum_def
      ; struct_def
      ; uninterp_def
      ; attr_def
      ; elem_def
      ; func_def
      ; mod_def
      ])
let file_parser = top_level <* whitespace

let parse_file (filename : string) : (topLevel list, string) result =
  let ch = open_in filename
  in let s = really_input_string ch (in_channel_length ch)
  in close_in ch
  ; Angstrom.parse_string ~consume:All file_parser s

let rec parse_files (files : string list) : (topLevel list list, string) result =
  match files with
  | [] -> Ok []
  | f :: fs ->
      match parse_file f, parse_files fs with
      | Ok res_f, Ok res_fs -> Ok (res_f :: res_fs)
      | Error msg, Ok _ -> Error (Printf.sprintf "Error in file %s%s" f msg)
      | Ok _, Error msg -> Error msg
      | Error msg_f, Error msg_fs ->
          Error (Printf.sprintf "Error in file %s%s\n%s" f msg_f msg_fs)
