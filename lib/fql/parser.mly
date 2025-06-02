%token EOF
%token SEMI DOT COMMA EQ
%token <string> ID STR
%token IF THEN ELSE
%token AND OR IS EQUALS EXISTS REQUIRED NOT

%token AT FOR FROM IN INTO TO WITH

%token BACKUP CLONE COPY CREATE DELETE DISABLE DOWNLOAD ENABLE ENSURE INSTALL
%token MOVE RESTART SET START STOP UNINSTALL WRITE

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

action: BACKUP category    { Backup $2 }
      | CLONE category     { Clone $2 }
      | COPY category      { Copy $2 }
      | CREATE category    { Create $2 }
      | DELETE category    { Delete $2 }
      | DISABLE category   { Disable $2 }
      | DOWNLOAD category  { Download $2 }
      | ENABLE category    { Enable $2 }
      | ENSURE cond        { Ensure $2 }
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
arg_sep: AT   { "at" }
       | FOR  { "for" }
       | FROM { "from" }
       | IN   { "in" }
       | INTO { "into" }
       | TO   { "to" }
       | WITH { "with" }
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
cat_id: ID        { $1 }
      | STR       { $1 }

      | AND       { "and" }
      | BACKUP    { "backup" }
      | CLONE     { "clone" }
      | COPY      { "copy" }
      | CREATE    { "create" }
      | DELETE    { "delete" }
      | DISABLE   { "disable" }
      | DOWNLOAD  { "download" }
      | ENABLE    { "enable" }
      | ENSURE    { "ensure" }
      | EQUALS    { "equals" }
      | EXISTS    { "exists" }
      | IF        { "if" }
      | INSTALL   { "install" }
      | IS        { "is" }
      | MOVE      { "move" }
      | NOT       { "not" }
      | OR        { "or" }
      | REQUIRED  { "required" }
      | RESTART   { "restart" }
      | SET       { "set" }
      | START     { "start" }
      | STOP      { "stop" }
      | UNINSTALL { "uninstall" }
      | WRITE     { "write" }
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
expr_id: ID         { $1 }
       | STR        { $1 }
 
       | BACKUP     { "backup" }
       | CLONE      { "clone" }
       | COPY       { "copy" }
       | CREATE     { "create" }
       | DELETE     { "delete" }
       | DISABLE    { "disable" }
       | DOWNLOAD   { "download" }
       | ENABLE     { "enable" }
       | ENSURE     { "ensure" }
       | IF         { "if" }
       | INSTALL    { "install" }
       | MOVE       { "move" }
       | RESTART    { "restart" }
       | SET        { "set" }
       | START      { "start" }
       | STOP       { "stop" }
       | UNINSTALL  { "uninstall" }
       | WRITE      { "write" }
       ;
