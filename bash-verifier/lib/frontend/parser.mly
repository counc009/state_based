%{
  open Ast

  let prod_type (ts : Ast.typ list) : Ast.typ =
    match ts with
    | [] -> Void
    | _ -> Product ts

  let prod_expr (es : Ast.expr list) : Ast.expr =
    match es with
    | [] -> UnitLit
    | [e] -> e
    | _ -> TupleExp es
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
%token STRUCT
%token THEN
%token TOUCH
%token TRY
%token TYPE
%token UNINTERPRETED
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
%token ASSIGN
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
%token FISHTAIL
%token SINGLEARROW
%token DOUBLEARROW

%token EOF

(* ELSE sets the precedence for conditional expressions *)
%right ELSE
%left LOGOR
%left LOGAND
%left BITOR
%left BITXOR
%left BITAND
%left EQ NE
%left LT LE GT GE
%left LSHIFT RSHIFT
%left ADD SUB
%left MUL DIV MOD
%right UMINUS LOGNOT BITNOT
%right EXISTS
(* LPAREN sets the precedence for function application *)
%left DOT LPAREN

%start program

%type <Ast.decl list>         program
%type <Ast.decl>              decl
%type <string list>           type_args
%type <Ast.typ list>          type_vars
%type <string * Ast.typ list> enum_case
%type <string * Ast.typ>      struct_field
%type <string * Ast.typ>      arg
%type <Ast.typ>               return_type
%type <Ast.typ>               nameannt_typ
%type <Ast.typ>               typ
%type <Ast.stmt>              stmt
%type <Ast.stmt list>         block
%type <(string * string list * Ast.stmt list) option> catch_block
%type <Ast.pattern * Ast.stmt list> match_case
%type <Ast.expr>              lval
%type <Ast.expr>              expr
%type <string * Ast.expr>     field

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

type_vars:
  |                                               { [] }
  | FISHTAIL; ts = sep_list(COMMA, typ); GT { ts }

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
  | LPAREN; args = sep_list(COMMA, typ); RPAREN; SINGLEARROW; ret = typ
      { Function (ret, args) }
  | STATE { StateRef }
  | LPAREN; ts = sep_list (COMMA, typ); RPAREN  { prod_type ts }
  | n = ID; ts = type_vars { Named (n, ts) }

stmt:
  | FOR; v = ID; IN; e = expr; body = block
    { ForLoop (v, e, body) }
  | IF; c = expr; th = block; es = opt_block(ELSE)
    { IfThenElse (c, th, es) }
  | MATCH; e = expr; LCURLY; cs = list(match_case); RCURLY
    { Match (e, cs) }
  | TRY; LCURLY; body = list(stmt); RCURLY; catch = catch_block;
      finally = opt_block(FINALLY)
    { TryCatch (body, catch, finally) }
  | CLEAR; e = expr; SEMICOLON
    { Clear e }
  | TOUCH; e = expr; SEMICOLON
    { Touch e }
  | ASSERT; e = expr; SEMICOLON
    { Assert e }
  | RETURN; e = expr; SEMICOLON
    { Return e }
  | YIELD; e = expr; SEMICOLON
    { Yield e }
  | RAISE; v = ID; SEMICOLON
    { Raise (v, []) }
  | RAISE; v = ID; LPAREN; e = sep_list(COMMA, expr); RPAREN
    { Raise (v, e) }
  | lhs = lval; ASSIGN; rhs = expr; SEMICOLON
    { Assign (lhs, rhs) }
  | LET; v = ID; ASSIGN; rhs = expr; SEMICOLON
    { LetStmt (v, None, rhs) }
  | LET; v = ID; COLON; t = typ; ASSIGN; rhs = expr; SEMICOLON
    { LetStmt (v, Some t, rhs) }
  | LOCALIZE; b = block
    { Localize b }

block:
  | LCURLY; body = list(stmt); RCURLY { body }

catch_block:
  | { None }
  | CATCH; e=ID; body = block
    { Some (e, [], body) }
  | CATCH; e=ID; LPAREN; vs = sep_list(COMMA, ID); RPAREN; body = block
    { Some (e, vs, body) }

opt_block(label):
  |                     { [] }    [@name absent]
  | label; body = block { body } [@name present]

match_case:
  | enum = ID; COLONCOLON; constr = ID; DOUBLEARROW; b = block
    { ({ enum; constr; vars = [] }, b) }
  | enum = ID; COLONCOLON; constr = ID;
      LPAREN; vars = sep_list(COMMA, ID); RPAREN; b = block
    { ({ enum; constr; vars }, b) }

lval:
  | v = ID
    { Id v }
  | l = lval; DOT; f = ID
    { FieldExp (l, f) }
  | l = lval; DOT; f = INTLIT
    { ProdField (l, int_of_string f) }
  | f = lval; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (f, [], es) }
  | f = ID; FISHTAIL; tys = sep_list(COMMA, typ); GT;
      LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (Id f, tys, es) }

expr:
  | v = ID
    { Id v }
  | b = BOOLLIT
    { BoolLit b }
  | i = INTLIT
    { IntLit i }
  | f = FLOATLIT
    { FloatLit f }
  | s = STRINGLIT
    { StringLit s }
  | c = CHARLIT
    { CharLit c }
  | LPAREN; es = sep_list(COMMA, expr); RPAREN
    { prod_expr es }
  | e = expr; DOT; f = ID
    { FieldExp (e, f) }
  | e = expr; DOT; f = INTLIT
    { ProdField (e, int_of_string f) }
  | FOR; v = ID; IN; e = expr; b = block
    { ForEach (v, e, b) }

  | SUB; e = expr %prec UMINUS
    { UnaryExp (Neg, e) }
  | LOGNOT; e = expr
    { UnaryExp (LNot, e) }
  | BITNOT; e = expr
    { UnaryExp (BNot, e) }

  | l = expr; ADD; r = expr
    { BinaryExp (l, Add, r) }
  | l = expr; SUB; r = expr
    { BinaryExp (l, Sub, r) }
  | l = expr; MUL; r = expr
    { BinaryExp (l, Mul, r) }
  | l = expr; DIV; r = expr
    { BinaryExp (l, Div, r) }
  | l = expr; MOD; r = expr
    { BinaryExp (l, Mod, r) }
  | l = expr; LSHIFT; r = expr
    { BinaryExp (l, LShft, r) }
  | l = expr; RSHIFT; r = expr
    { BinaryExp (l, RShft, r) }
  | l = expr; LT; r = expr
    { BinaryExp (l, Lt, r) }
  | l = expr; LE; r = expr
    { BinaryExp (l, Le, r) }
  | l = expr; GT; r = expr
    { BinaryExp (l, Gt, r) }
  | l = expr; GE; r = expr
    { BinaryExp (l, Ge, r) }
  | l = expr; EQ; r = expr
    { BinaryExp (l, Eq, r) }
  | l = expr; NE; r = expr
    { BinaryExp (l, Ne, r) }
  | l = expr; BITAND; r = expr
    { BinaryExp (l, BAnd, r) }
  | l = expr; BITXOR; r = expr
    { BinaryExp (l, BXor, r) }
  | l = expr; BITOR; r = expr
    { BinaryExp (l, BOr, r) }
  | l = expr; LOGAND; r = expr
    { BinaryExp (l, LAnd, r) }
  | l = expr; LOGOR; r = expr
    { BinaryExp (l, LOr, r) }

  | enum = ID; tys = type_vars; COLONCOLON;
      constr = ID; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { EnumExp (enum, tys, constr, es) }
  | f = expr; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (f, [], es) }
  (* We can only apply type variables directly to a name, there's also a
   * shift/reduce conflict without this rule because ID FISHTAIL has to be
   * reduced to expr FISHTAIL for function application but not for an enum *)
  | f = ID; FISHTAIL; tys = sep_list(COMMA, typ); GT;
      LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (Id f, tys, es) }

  | IF; c = expr; THEN; th = expr; ELSE; el = expr
    { CondExp (c, th, el) }
  | EXISTS; e = expr
    { Exists e }

  (*
  | s = ID; tys = type_vars; LCURLY; fs = sep_list(COMMA, field); RCURLY
    { StructExp (s, tys, fs) }
  *)

  (* TODO: Structs *)

field:
  | n = ID; ASSIGN; e = expr
    { (n, e) }
