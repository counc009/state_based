%token BACKUP CLONE COPY CREATE DELETE DISABLE DOWNLOAD ENABLE ENSURE INSTALL MOVE SET START STOP RESTART UNINSTALL WRITE
%token DEFAULT DIR ENVIRONMENT FILE FILES GITHUB GROUP PACKAGE PASSWORD PERMISSIONS REPO SHELL STRING SUDO USER VARIABLE VIRTUAL
%token EXISTS REQUIRES
%token IF THEN ELSE AND OR
%token DOT SEMI EQ

%token <string> STR_LIT ID

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND
%left EQ

%start top

%%
top:                              { }
   | base                         { }
   | base DOT top                 { }
   ;

base: atom                        { }
    | atom SEMI base              { }
    | atom SEMI AND atom          { }
    | IF cond THEN base           { }
    | IF cond THEN base ELSE base { }
    ;

(* selector ::= for ??? *)
atom: action selector? args { }
    ;

action: CREATE category    { }
      | DELETE category    { }
      | SET category       { }
      | CLONE category     { }
      | INSTALL category   { }
      | UNINSTALL category { }
      | WRITE category     { }
      | DISABLE category   { }
      | COPY category      { }
      | MOVE category      { }
      | RESTART            { }
      | ENSURE cond        { }
      | BACKUP category    { }
      | DOWNLOAD category  { }
      | ENABLE category    { }
      | START category     { }
      | STOP category      { }
      ;

(* I'm wondering more and more if category is just a series of words that we
 * later interpret the meaning of *)
category: FILE  { }
        | FILES { }
        | DIR   { }
        | VIRTUAL ENVIRONMENT { }
        | ENVIROMENT VARIABLE { }
        | FILE PERMISSIONS { }
        | GITHUB REPO { }
        (* PACKAGE name | PACKAGES names *)
        | PACKAGE { }
        | STRING STR_LIT { }
        | PASSWORD { }
        | DEFAULT SHELL { }
        | USER { }
        | GROUP { }
        | SUDO { }
        ;

cond: cond AND cond   { }
    | cond OR cond    { }
    | expr IS expr    { }
    | category EXISTS { }
    | category NOT EXISTS { }
    | category REQUIRED { }
    | category NOT REQUIRED
    ;

expr: ID      { }
    | STR_LIT { }
    ;

(* THEORY: actually should be
 * existential ::= category EXISTS
 * and that we need to be able to add descriptors before many (all?) categories
 *)
existential: EXISTS            { }
           | extid existential { }
           ;
(* All non-exists keywords *)
extid: ???
     ;
