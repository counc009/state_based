%{
  open Stdint
  open Ast.Parsed

  let prod_type (ts : typ list) : typ_base =
    match ts with
    | [] -> Void
    | _   -> Product ts

  let prod_expr (es : expr list) : expr_base =
    match es with
    | []  -> UnitLit
    | [e] -> e.ast
    | _   -> TupleExp es
%}

%token <string> ID
%token UNDERSCORE

%token <bool>   BOOLLIT
%token <string> STRINGLIT
%token <char>   CHARLIT

%token <Stdint.int8>   INT8LIT
%token <Stdint.int16>  INT16LIT
%token <Stdint.int32>  INT32LIT
%token <Stdint.int64>  INT64LIT
%token <Stdint.uint8>  UINT8LIT
%token <Stdint.uint16> UINT16LIT
%token <Stdint.uint32> UINT32LIT
%token <Stdint.uint64> UINT64LIT
%token <int>    INTLIT
%token <F32.t> FLOAT32LIT
%token <float> FLOAT64LIT

%token AS
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
%token FORALL
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
%token WHILE
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
%token STRING
%token STATE
%token LIST

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
%left AS
%right UMINUS LOGNOT BITNOT
%right EXISTS
(* LPAREN sets the precedence for function application *)
%left DOT LPAREN

%start program

%type <decl list>         program
%type <decl>              decl
%type <decl_base>         decl_base
%type <name list>         type_args
%type <typ list>          type_vars
%type <name * typ list>   enum_case
%type <name * typ>        struct_field
%type <name * typ>        arg
%type <typ>               return_type
%type <typ>               nameannt_typ
%type <typ>               typ
%type <typ_base>          typ_base
%type <stmt>              stmt
%type <stmt_base>         stmt_base
%type <stmt list>         block
%type <stmt list>         default_case
%type <expr>              lval
%type <expr_base>         lval_base
%type <expr>              ns_expr
%type <expr_base>         ns_expr_base
%type <expr>              expr
%type <expr_base>         expr_base
%type <name * expr>       field
%type <string>            id
%type <name>              name
%type <name>              idname
%type <(name * name list * stmt list) option> catch_block
%type <pattern * stmt list>                   match_case

%%

program:
  | decls=list(decl); EOF { decls }

(* We define our own seperated lists that allows trailing seperators *)
sep_list(seperator, X):
  |                                               { [] }      [@name none]
  | x = X                                         { [ x ] }   [@name one]
  | x = X; seperator; xs = sep_list(seperator, X) { x :: xs } [@name more]

decl: d = decl_base { { ast = d; pos = $loc } }

decl_base:
  | ENUM; name = name; ty_args = type_args;
      LCURLY; constrs = sep_list(COMMA, enum_case); RCURLY
    { Enum { name; ty_args; constrs } }
  | STRUCT; name = name; ty_args = type_args;
      LCURLY; fields = sep_list(COMMA, struct_field); RCURLY
    { Struct { name; ty_args; fields } }
  | TYPE; name = name; ASSIGN; def = typ
    { Type { name; def } }
  | UNINTERPRETED; name = name; ty_args = type_args;
      LPAREN; args = sep_list(COMMA, nameannt_typ); RPAREN;
      SINGLEARROW; ret = typ
    { Uninterp { name; ty_args; args; ret } }
  | ATTRIBUTE; name = name; COLON; ty = typ
    { Attribute { local = false; name; ty } }
  | LOCAL; ATTRIBUTE; name = name; COLON; ty = typ
    { Attribute { local = true; name; ty } }
  | ELEMENT; name = name; LPAREN; ty = sep_list(COMMA, nameannt_typ); RPAREN
    { Element { local = false; name; ty } }
  | LOCAL; ELEMENT; name = name; LPAREN; ty = sep_list(COMMA, nameannt_typ);
      RPAREN
    { Element { local = true; name; ty } }
  | EXCEPTION; name = name; LPAREN; ty = sep_list(COMMA, nameannt_typ); RPAREN
    { Exception { name; ty } }
  | FN; name = name; ty_args = type_args;
      LPAREN; args = sep_list(COMMA, arg); RPAREN;
      ret = return_type;
      LCURLY; body = list(stmt); RCURLY
    { Function { name; ty_args; args; ret; body } }

type_args:
  |                                     { [] }
  | LT; ts = sep_list(COMMA, name); GT  { ts }

type_vars:
  |                                               { [] }
  | FISHTAIL; ts = sep_list(COMMA, typ); GT { ts }

enum_case:
  | nm = name
    { (nm, []) }
  | nm = name; LPAREN; tys = sep_list(COMMA, nameannt_typ); RPAREN
    { (nm, tys) }

struct_field:
  | nm = name; COLON; ty = typ  { (nm, ty) }

arg:
  | n = name; COLON; t = typ { (n, t) }

return_type:
  |                       { { ast = Void; pos = $loc } }
  | SINGLEARROW; t = typ  { t }

nameannt_typ:
  | t = typ             { t }
  | ID; COLON; t = typ  { t }

typ: t = typ_base { { ast = t; pos = $loc } }

typ_base:
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
  | STRING  { String }
  | LPAREN; args = sep_list(COMMA, typ); RPAREN; SINGLEARROW; ret = typ
      { Function (ret, args) }
  | STATE { StateRef }
  | LPAREN; ts = sep_list (COMMA, typ); RPAREN  { prod_type ts }
  | LIST; FISHTAIL; t = typ; GT { List t }
  | n = ID; ts = type_vars { Named (n, ts) }

stmt: s = stmt_base { { ast = s; pos = $loc } }

stmt_base:
  | FOR; v = idname; IN; e = ns_expr; body = block
    { ForLoop (v, e, body) }
  | FORALL; elem = idname; LPAREN; vs = sep_list(COMMA, idname); RPAREN;
    base = option(preceded(IN, ns_expr)); body = block
    { ForElem (base, elem, vs, body) }
  | WHILE; c = ns_expr; body = block
    { WhileLoop (c, body) }
  | IF; c = ns_expr; th = block; es = opt_block(ELSE)
    { IfThenElse (c, th, es) }
  | MATCH; e = ns_expr; LCURLY; cs = list(match_case);
      d = loption(default_case); RCURLY
    { Match (e, (cs, d)) }
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
  | RAISE; v = name; SEMICOLON
    { Raise (v, []) }
  | RAISE; v = name; LPAREN; e = sep_list(COMMA, expr); RPAREN
    { Raise (v, e) }
  | lhs = lval; ASSIGN; rhs = expr; SEMICOLON
    { Assign (lhs, rhs) }
  | LET; v = idname; ASSIGN; rhs = expr; SEMICOLON
    { LetStmt (v, None, rhs) }
  | LET; v = idname; COLON; t = typ; ASSIGN; rhs = expr; SEMICOLON
    { LetStmt (v, Some t, rhs) }
  | LOCALIZE; b = block
    { Localize b }

block:
  | LCURLY; body = list(stmt); RCURLY { body }

catch_block:
  | { None }
  | CATCH; e=name; body = block
    { Some (e, [], body) }
  | CATCH; e=name; LPAREN; vs = sep_list(COMMA, name); RPAREN; body = block
    { Some (e, vs, body) }

opt_block(label):
  |                     { [] }    [@name absent]
  | label; body = block { body } [@name present]

match_case:
  | enum = name; COLONCOLON; constr = name; DOUBLEARROW; b = block
    { ({ ast = { enum; constr; vars = [] };
         pos = ($startpos(enum), $endpos(constr)) },
        b) }
  | enum = name; COLONCOLON; constr = name;
      LPAREN; vars = sep_list(COMMA, idname); RPAREN; c = DOUBLEARROW;
      b = block
    { ({ ast = { enum; constr; vars };
         pos = ($startpos(enum), $endpos(c)) },
        b) }

default_case:
  | UNDERSCORE; DOUBLEARROW; b = block { b }

lval: l = lval_base { { ast = l; pos = $loc } }

lval_base:
  | v = ID
    { Id v }
  | l = lval; DOT; f = name
    { FieldExp (l, f) }
  | l = lval; DOT; f = INTLIT
    { ProdField (l, { ast = f; pos = $loc(f) }) }
  | f = lval; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (f, [], es) }
  | f = ID; FISHTAIL; tys = sep_list(COMMA, typ); GT;
      LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp ({ ast = Id f; pos = $loc(f) }, tys, es) }

(* Non-struct expressions *)
ns_expr: e = ns_expr_base { { ast = e; pos = $loc } }

ns_expr_base:
  | v = ID
    { Id v }
  | b = BOOLLIT
    { BoolLit b }
  | s = STRINGLIT
    { StringLit s }
  | c = CHARLIT
    { CharLit c }

  | i = INTLIT
    { Int64Lit (Int64.of_int i) }
  | i = INT8LIT
    { Int8Lit i }
  | i = INT16LIT
    { Int16Lit i }
  | i = INT32LIT
    { Int32Lit i }
  | i = INT64LIT
    { Int64Lit i }
  | i = UINT8LIT
    { UInt8Lit i }
  | i = UINT16LIT
    { UInt16Lit i }
  | i = UINT32LIT
    { UInt32Lit i }
  | i = UINT64LIT
    { UInt64Lit i }

  | f = FLOAT32LIT
    { F32Lit f }
  | f = FLOAT64LIT
    { F64Lit f }

  (* Inside parentheses we can include struct expressions *)
  | LPAREN; es = sep_list(COMMA, expr); RPAREN
    { prod_expr es }
  | e = ns_expr; DOT; f = name
    { FieldExp (e, f) }
  | e = ns_expr; DOT; f = INTLIT
    { ProdField (e, { ast = f; pos = $loc(f) }) }
  | e = ns_expr; AS; t = typ
    { CastExp (e, t) }
  | FOR; v = idname; IN; e = ns_expr; b = block
    { ForEach (v, e, b) }
  | FORALL; elem = idname; LPAREN; vs = sep_list(COMMA, idname); RPAREN;
    base = option(preceded(IN, ns_expr)); b = block
    { ForAll (base, elem, vs, b) }

  | SUB; e = ns_expr %prec UMINUS
    { UnaryExp (Neg, e) }
  | LOGNOT; e = ns_expr
    { UnaryExp (LNot, e) }
  | BITNOT; e = ns_expr
    { UnaryExp (BNot, e) }

  | l = ns_expr; ADD; r = ns_expr
    { BinaryExp (l, Add, r) }
  | l = ns_expr; SUB; r = ns_expr
    { BinaryExp (l, Sub, r) }
  | l = ns_expr; MUL; r = ns_expr
    { BinaryExp (l, Mul, r) }
  | l = ns_expr; DIV; r = ns_expr
    { BinaryExp (l, Div, r) }
  | l = ns_expr; MOD; r = ns_expr
    { BinaryExp (l, Mod, r) }
  | l = ns_expr; LSHIFT; r = ns_expr
    { BinaryExp (l, LShft, r) }
  | l = ns_expr; RSHIFT; r = ns_expr
    { BinaryExp (l, RShft, r) }
  | l = ns_expr; LT; r = ns_expr
    { BinaryExp (l, Lt, r) }
  | l = ns_expr; LE; r = ns_expr
    { BinaryExp (l, Le, r) }
  | l = ns_expr; GT; r = ns_expr
    { BinaryExp (l, Gt, r) }
  | l = ns_expr; GE; r = ns_expr
    { BinaryExp (l, Ge, r) }
  | l = ns_expr; EQ; r = ns_expr
    { BinaryExp (l, Eq, r) }
  | l = ns_expr; NE; r = ns_expr
    { BinaryExp (l, Ne, r) }
  | l = ns_expr; BITAND; r = ns_expr
    { BinaryExp (l, BAnd, r) }
  | l = ns_expr; BITXOR; r = ns_expr
    { BinaryExp (l, BXor, r) }
  | l = ns_expr; BITOR; r = ns_expr
    { BinaryExp (l, BOr, r) }
  | l = ns_expr; LOGAND; r = ns_expr
    { BinaryExp (l, LAnd, r) }
  | l = ns_expr; LOGOR; r = ns_expr
    { BinaryExp (l, LOr, r) }

  | enum = name; tys = type_vars; COLONCOLON;
      constr = name; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { EnumExp (enum, tys, constr, es) }
  | f = ns_expr; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (f, [], es) }
  (* We can only apply type variables directly to a name, there's also a
   * shift/reduce conflict without this rule because ID FISHTAIL has to be
   * reduced to expr FISHTAIL for function application but not for an enum *)
  | f = ID; FISHTAIL; tys = sep_list(COMMA, typ); GT;
      LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp ({ ast = Id f; pos = $loc(f) }, tys, es) }

  | IF; c = ns_expr; THEN; th = ns_expr; ELSE; el = ns_expr
    { CondExp (c, th, el) }
  | EXISTS; e = ns_expr
    { Exists e }

expr: e = expr_base { { ast = e; pos = $loc } }

expr_base:
  | v = ID
    { Id v }
  | b = BOOLLIT
    { BoolLit b }
  | s = STRINGLIT
    { StringLit s }
  | c = CHARLIT
    { CharLit c }

  | i = INTLIT
    { Int64Lit (Int64.of_int i) }
  | i = INT8LIT
    { Int8Lit i }
  | i = INT16LIT
    { Int16Lit i }
  | i = INT32LIT
    { Int32Lit i }
  | i = INT64LIT
    { Int64Lit i }
  | i = UINT8LIT
    { UInt8Lit i }
  | i = UINT16LIT
    { UInt16Lit i }
  | i = UINT32LIT
    { UInt32Lit i }
  | i = UINT64LIT
    { UInt64Lit i }

  | f = FLOAT32LIT
    { F32Lit f }
  | f = FLOAT64LIT
    { F64Lit f }

  | LPAREN; es = sep_list(COMMA, expr); RPAREN
    { prod_expr es }
  | e = expr; DOT; f = name
    { FieldExp (e, f) }
  | e = expr; DOT; f = INTLIT
    { ProdField (e, { ast = f; pos = $loc(f) }) }
  | e = expr; AS; t = typ
    { CastExp (e, t) }
  | FOR; v = idname; IN; e = ns_expr; b = block
    { ForEach (v, e, b) }
  | FORALL; elem = idname; LPAREN; vs = sep_list(COMMA, idname); RPAREN;
    base = option(preceded(IN, ns_expr)); b = block
    { ForAll (base, elem, vs, b) }

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

  | enum = name; tys = type_vars; COLONCOLON;
      constr = name; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { EnumExp (enum, tys, constr, es) }
  | f = expr; LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp (f, [], es) }
  | f = ID; FISHTAIL; tys = sep_list(COMMA, typ); GT;
      LPAREN; es = sep_list(COMMA, expr); RPAREN
    { FuncExp ({ ast = Id f; pos = $loc(f) }, tys, es) }

  | IF; c = expr; THEN; th = expr; ELSE; el = expr
    { CondExp (c, th, el) }
  | EXISTS; e = expr
    { Exists e }

  | s = ID; tys = type_vars; LCURLY; fs = sep_list(COMMA, field); RCURLY
    { StructExp ({ ast = s; pos = $loc(s) }, tys, fs) }

field:
  | n = name; ASSIGN; e = expr
    { (n, e) }

id:
  | n = ID     { n }
  | UNDERSCORE { "_" }

idname: i = id { { ast = i; pos = $loc } }
name: i = ID { { ast = i; pos = $loc } }
