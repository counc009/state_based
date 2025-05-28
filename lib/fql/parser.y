%token ATOM EXPR IF ';' '.'

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND
%left '='

%%

top: %empty
   | base
   | base '.' top
   ;

base: atom
    | atom ';' base
    | atom ';' AND atom
    | IF cond THEN base
    | IF cond THEN base ELSE base
    ;

atom: ATOM
    ;

cond: cond AND cond
    | cond OR cond
    | expr '=' expr
    ;
expr: EXPR
    ;

%%
