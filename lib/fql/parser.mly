%token CLONE COPY CREATE DELETE DISABLE INSTALL MOVE SET RESTART WRITE
%token DEFAULT DIR ENVIRONMENT FILE FILES GITHUB PACKAGE PASSWORD PERMISSIONS REPO SHELL STRING VARIABLE VIRTUAL
%token IF THEN ELSE AND OR

%token <string> STR_LIT

%start top

%%
top:                              { }
   | base                         { }
   | base DOT top                 { }
   ;

base: atom                        { }
    | atom SEMI base              { }
    | IF cond THEN base           { }
    | IF cond THEN base ELSE base { }
    ;

action: CREATE category  { }
      | DELETE category  { }
      | SET category     { }
      | CLONE category   { }
      | INSTALL category { }
      | WRITE category   { }
      | DISABLE category { }
      | COPY category    { }
      | MOVE category    { }
      | RESTART          { }
      | CHECK cond       { }
      ;

category: FILE  { }
        | FILES { }
        | DIR   { }
        | VIRTUAL ENVIRONMENT { }
        | ENVIROMENT VARIABLE { }
        | FILE PERMISSIONS { }
        | GITHUB REPO { }
        | PACKAGE { }
        | STRING STR_LIT { }
        | PASSWORD { }
        | DEFAULT SHELL { }
        ;
