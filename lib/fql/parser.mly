%token EOF
%token SEMI DOT COMMA EQ
%token <string> ID STR UNKNOWN
%token IF THEN ELSE
%token AND OR IS EQUALS EXISTS REQUIRED NOT

%token AT FOR FROM IN INTO TO WITH

%token CLONE COPY CREATE DELETE DISABLE DOWNLOAD ENABLE INSTALL MOVE
%token RESTART SET START STOP UNINSTALL WRITE

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND

%start query
%type <Ast.top> query

%%

query: top EOF { $1 };

top:                              { [] }
   | base                         { [$1] }
   | base DOT top                 { $1 :: $3 }
   ;

base: atom                        { Cons ($1, Nil) }
    | atom SEMI base              { Cons ($1, $3) }
    | atom SEMI AND atom          { Cons ($1, Cons ($4, Nil)) }
    | IF cond THEN base           { If ($2, $4, Nil) }
    | IF cond THEN base ELSE base { If ($2, $4, $6) }
    ;

atom: action args { ($1, $2) };

action: CLONE category     { Clone $2 }
      | COPY category      { Copy $2 }
      | CREATE category    { Create $2 }
      | DELETE category    { Delete $2 }
      | DISABLE category   { Disable $2 }
      | DOWNLOAD category  { Download $2 }
      | ENABLE category    { Enable $2 }
      | INSTALL category   { Install $2 }
      | MOVE category      { Move $2 }
      | RESTART            { Restart }
      | SET category       { Set $2 }
      | START category     { Start $2 }
      | STOP category      { Stop $2 }
      | UNINSTALL category { Uninstall $2 }
      | WRITE category     { Write $2 }
      ;

args:           { [] }
    | arg args  { $1 @ $2 }
    ;
arg: arg_sep arg_vals { $2 $1 };
arg_sep: AT   { Ast.Str "at" }
       | FOR  { Str "for" }
       | FROM { Str "from" }
       | IN   { Str "in" }
       | INTO { Str "into" }
       | TO   { Str "to" }
       | WITH { Str "with" }
       ;
arg_vals: category { fun nm -> [([nm], $1)] }
        | arg_defs { fun _ -> $1 }
        ;
arg_defs: category EQ category                { [($1, $3)] }
        | category EQ category COMMA arg_defs { ($1, $3) :: $5 }
        ;

category: cat_id cat { $1 :: $2 };
cat:            { [] }
   | cat_id cat { $1 :: $2 }
   ;
cat_id: ID        { Str $1 }
      | STR       { Str $1 }
      | UNKNOWN   { Unknown $1 }

      | AND       { Str "and" }
      | CLONE     { Str "clone" }
      | COPY      { Str "copy" }
      | CREATE    { Str "create" }
      | DELETE    { Str "delete" }
      | DISABLE   { Str "disable" }
      | DOWNLOAD  { Str "download" }
      | ENABLE    { Str "enable" }
      | EQUALS    { Str "equals" }
      | EXISTS    { Str "exists" }
      | IF        { Str "if" }
      | INSTALL   { Str "install" }
      | IS        { Str "is" }
      | MOVE      { Str "move" }
      | NOT       { Str "not" }
      | OR        { Str "or" }
      | REQUIRED  { Str "required" }
      | RESTART   { Str "restart" }
      | SET       { Str "set" }
      | START     { Str "start" }
      | STOP      { Str "stop" }
      | UNINSTALL { Str "uninstall" }
      | WRITE     { Str "write" }
      ;

cond: cond AND cond         { And ($1, $3) }
    | cond OR cond          { Or ($1, $3) }
    | expr IS expr          { Eq ($1, $3) }
    | expr IS NOT expr      { Not (Eq ($1, $4)) }
    | expr EQUALS expr      { Eq ($1, $3) }
    | expr NOT EQUALS expr  { Not (Eq ($1, $4)) }
    | expr EXISTS           { Exists $1 }
    | expr NOT EXISTS       { Not (Exists $1) }
    | expr REQUIRED         { Required $1 }
    | expr NOT REQUIRED     { Not (Required $1) }
    ;

expr: expr_id exp { $1 :: $2 };
exp:              { [] }
   | expr_id exp  { $1 :: $2 }
   ;
expr_id: ID         { Str $1 }
       | STR        { Str $1 }
       | UNKNOWN    { Unknown $1 }
 
       | CLONE      { Str "clone" }
       | COPY       { Str "copy" }
       | CREATE     { Str "create" }
       | DELETE     { Str "delete" }
       | DISABLE    { Str "disable" }
       | DOWNLOAD   { Str "download" }
       | ENABLE     { Str "enable" }
       | IF         { Str "if" }
       | INSTALL    { Str "install" }
       | MOVE       { Str "move" }
       | RESTART    { Str "restart" }
       | SET        { Str "set" }
       | START      { Str "start" }
       | STOP       { Str "stop" }
       | UNINSTALL  { Str "uninstall" }
       | WRITE      { Str "write" }
       ;
