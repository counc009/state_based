%token EOF
%token SEMI DOT COMMA EQ
%token <string> ID STR UNKNOWN
%token IF THEN ELSE
%token AND OR IS EQUALS EXISTS INSTALLED REQUIRED RUNNING NOT

%token AT FOR FROM IN INTO TO VIA WITH

%token CLONE COPY CREATE DELETE DISABLE DOWNLOAD ENABLE INSTALL MOVE
%token REBOOT SET START STOP UNINSTALL WRITE

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND

%start query
%type <ParseTree.top> query

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
      | REBOOT             { Reboot }
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
arg_sep: AT   { ParseTree.Str "at" }
       | FOR  { Str "for" }
       | FROM { Str "from" }
       | IN   { Str "in" }
       | INTO { Str "into" }
       | TO   { Str "to" }
       | VIA  { Str "via" }
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
      | INSTALLED { Str "installed" }
      | IF        { Str "if" }
      | INSTALL   { Str "install" }
      | IS        { Str "is" }
      | MOVE      { Str "move" }
      | NOT       { Str "not" }
      | OR        { Str "or" }
      | REQUIRED  { Str "required" }
      | REBOOT    { Str "reboot" }
      | RUNNING   { Str "running" }
      | SET       { Str "set" }
      | START     { Str "start" }
      | STOP      { Str "stop" }
      | UNINSTALL { Str "uninstall" }
      | WRITE     { Str "write" }
      ;

cond: cond AND cond         { And ($1, $3) }
    | cond OR cond          { Or ($1, $3) }
    | spec IS spec          { Eq ($1, $3) }
    | spec IS NOT spec      { Not (Eq ($1, $4)) }
    | spec EQUALS spec      { Eq ($1, $3) }
    | spec NOT EQUALS spec  { Not (Eq ($1, $4)) }
    | spec EXISTS           { Exists $1 }
    | spec NOT EXISTS       { Not (Exists $1) }
    | spec INSTALLED        { Installed $1 }
    | spec NOT INSTALLED    { Not (Installed $1) }
    | spec REQUIRED         { Required $1 }
    | spec NOT REQUIRED     { Not (Required $1) }
    | spec RUNNING          { Running $1 }
    | spec NOT RUNNING      { Not (Running $1) }
    ;

spec: expr spec_args { ($1, $2) };

spec_args:                    { [] }
         | spec_arg spec_args { $1 @ $2 }
         ;
spec_arg: arg_sep spec_argvs { $2 $1 };

spec_argvs: expr       { fun nm -> [([nm], $1)] }
          | spec_argds { fun _ -> $1 }
          ;
spec_argds: expr EQ expr                  { ($1, $3) :: [] }
          | expr EQ expr COMMA spec_argds { ($1, $3) :: $5 }
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
       | REBOOT     { Str "reboot" }
       | SET        { Str "set" }
       | START      { Str "start" }
       | STOP       { Str "stop" }
       | UNINSTALL  { Str "uninstall" }
       | WRITE      { Str "write" }
       ;
