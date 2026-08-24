%{
  open Ast

  let array_type (t : Ast.typ) (n : string) : Ast.typ =
    Array (t, int_of_string n)

  let prod_type (ts : Ast.typ list) : Ast.typ =
    match ts with
    | [] -> Void
    | _ -> Product ts
%}

%token <string> ID
%token <bool>   BOOLLIT
%token <string> INTLIT
%token <string> FLOATLIT
%token <string> STRINGLIT
%token <char>   CHARLIT

%token ASSERT
%token ATTRIBUTE
%token CATCH
%token CLEAR
%token ELEMENT
%token ELSE
%token ENUM
%token EXCEPTION
%token EXISTS
%token FINALLY
%token FN
%token FOR
%token IF
%token IN
%token LET
%token LOCAL
%token LOCALIZE
%token MATCH
%token RAISE
%token RETURN
%token SIZEOF
%token STRUCT
%token THEN
%token TOUCH
%token TRY
%token TYPE
%token UNINTERPRETED
%token UNION
%token YIELD

%token VOID
%token BOOL
%token INT8
%token INT16
%token INT32
%token INT64
%token UINT8
%token UINT16
%token UINT32
%token UINT64
%token FLOAT32
%token FLOAT64
%token ARRAY
%token PTR
%token STATE

%token LCURLY
%token RCURLY
%token LPAREN
%token RPAREN

%token COMMA
%token DOT
%token SEMICOLON
%token COLON

%token MUL
%token DIV
%token MOD
%token ADD
%token SUB
%token LSHIFT
%token RSHIFT
%token LT
%token LE
%token GT
%token GE
%token EQ
%token NE
%token BITAND
%token LOGAND
%token BITOR
%token LOGOR
%token BITXOR
%token BITNOT
%token LOGNOT

%token COLONCOLON
%token SINGLEARROW
%token DOUBLEARROW
%token UNIT

%token EOF

%start program

%type <Ast.decl list>         program
%type <Ast.decl>              decl
%type <string list>           type_args
%type <string * Ast.typ list> enum_case
%type <string * Ast.typ>      struct_field
%type <string * Ast.typ>      arg
%type <Ast.typ>               return_type
%type <Ast.typ>               nameannt_typ
%type <Ast.typ>               typ
%type <Ast.stmt>              stmt
%type <(string * string list * Ast.stmt list) option> catch_block

%%

program:
  | decls=list(decl); EOF { decls }

(* We define our own seperated lists that allows trailing seperators *)
sep_list(seperator, X):
  |                                               { [] }      [@name none]
  | x = X                                         { [ x ] }   [@name one]
  | x = X; seperator; xs = sep_list(seperator, X) { x :: xs } [@name more]

decl:
  | ENUM; name = ID; ty_args = type_args;
      LCURLY; constrs = sep_list(COMMA, enum_case); RCURLY
    { Enum { name; ty_args; constrs } }
  | STRUCT; name = ID; ty_args = type_args;
      LCURLY; fields = sep_list(COMMA, struct_field); RCURLY
    { Struct { name; ty_args; fields } }
  | TYPE; name = ID; EQ; def = typ
    { Type { name; def } }
  | UNINTERPRETED; name = ID; ty_args = type_args;
      LPAREN; args = sep_list(COMMA, nameannt_typ); RPAREN;
      SINGLEARROW; ret = typ
    { Uninterp { name; ty_args; args; ret } }
  | ATTRIBUTE; name = ID; COLON; ty = typ
    { Attribute { local = false; name; ty } }
  | LOCAL; ATTRIBUTE; name = ID; COLON; ty = typ
    { Attribute { local = true; name; ty } }
  | ELEMENT; name = ID; LPAREN; ty = sep_list(COMMA, nameannt_typ); RPAREN
    { Element { local = false; name; ty } }
  | LOCAL; ELEMENT; name = ID; LPAREN; ty = sep_list(COMMA, nameannt_typ); RPAREN
    { Element { local = true; name; ty } }
  | EXCEPTION; name = ID; LPAREN; ty = sep_list(COMMA, nameannt_typ); RPAREN
    { Exception { name; ty } }
  | FN; name = ID; ty_args = type_args;
      LPAREN; args = sep_list(COMMA, arg); RPAREN;
      ret = return_type;
      LCURLY; body = list(stmt); RCURLY
    { Function { name; ty_args; args; ret; body } }

type_args:
  |                                   { [] }
  | LT; ts = sep_list(COMMA, ID); GT  { ts }

enum_case:
  | nm = ID; LPAREN; tys = sep_list(COMMA, nameannt_typ); RPAREN { (nm, tys) }

struct_field:
  | nm = ID; COLON; ty = typ  { (nm, ty) }

arg:
  | n = ID; COLON; t = typ { (n, t) }

return_type:
  |                       { Void }
  | SINGLEARROW; t = typ  { t }

nameannt_typ:
  | t = typ             { t }
  | ID; COLON; t = typ  { t }

typ:
  | VOID    { Void }
  | BOOL    { Bool }
  | INT8    { SInt8 }
  | INT16   { SInt16 }
  | INT32   { SInt32 }
  | INT64   { SInt64 }
  | UINT8   { UInt8 }
  | UINT16  { UInt16 }
  | UINT32  { UInt32 }
  | UINT64  { UInt64 }
  | FLOAT32 { Float32 }
  | FLOAT64 { Float64 }
  | PTR; COLONCOLON; LT; t = typ; GT  { Pointer t }
  | ARRAY; COLONCOLON; LT; t = typ; COMMA; n = INTLIT; GT { array_type t n }
  | STRUCT; LCURLY; fs = sep_list(COMMA, struct_field); RCURLY { Struct fs }
  | UNION; LCURLY; fs = sep_list(COMMA, struct_field); RCURLY  { Union fs }
  | LPAREN; args = sep_list(COMMA, typ); RPAREN; SINGLEARROW; ret = typ
      { Function (ret, args) }
  | STATE { StateRef }
  | LPAREN; ts = sep_list (COMMA, typ); RPAREN  { prod_type ts }
  | n = ID  { Named (n, None) }
  | n = ID; COLONCOLON; LT; ts = sep_list(COMMA, typ); GT { Named (n, Some ts) }

stmt:
  (* TODO *)
  | TRY; LCURLY; body = list(stmt); RCURLY; catch = catch_block;
      finally = opt_block(FINALLY)
    { TryCatch (body, catch, finally) }

catch_block:
  | { None }
  | CATCH; e=ID; LCURLY; body = list(stmt); RCURLY 
    { Some (e, [], body) }
  | CATCH; e=ID; LPAREN; vs = sep_list(COMMA, ID); RPAREN;
      LCURLY; body = list(stmt); RCURLY
    { Some (e, vs, body) }

opt_block(label):
  |                                           { [] }    [@name absent]
  | label; LCURLY; body = list(stmt); RCURLY  { body }  [@name present]
