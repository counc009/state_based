%token ATOM COND IF ';' '.'

%nonassoc THEN
%nonassoc ELSE

%%

top: %empty
   | base
   | base '.' top
   ;

base: atom
    | atom ';' base
    | IF cond THEN base
    | IF cond THEN base ELSE base
    ;

atom: ATOM
    ;
cond: COND
    ;

%%
