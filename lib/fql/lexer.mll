{
  open Parser
}

rule token = parse
  | [' ''\t''\n'] { token lexbuf }

  | "clone"       { CLONE }
  | "copy"        { COPY }
  | "create"      { CREATE }
  | "disable"     { DISABLE }
  | "delete"      { DELETE }
  | "install"     { INSTALL }
  | "move"        { MOVE }
  | "restart"     { RESTART }
  | "set"         { SET }
  | "write"       { WRITE }

  | "default"     { DEFAULT }
  | "directory"   { DIR }
  | "environment" { ENVIRONMENT }
  | "file"        { FILE }
  | "files"       { FILES }
  | "github"      { GITHUB }
  | "package"     { PACKAGE }
  | "password"    { PASSWORD }
  | "permissions" { PERMISSIONS }
  | "repository"  { REPO }
  | "shell"       { SHELL }
  | "string"      { STRING }
  | "variable"    { VARIABLE }
  | "virtual"     { VIRTUAL }

  | "if"          { IF }
  | "then"        { THEN }
  | "otherwise"   { ELSE }
  | "and"         { AND }
  | "or"          { OR }

  | '"'[^'"']*'"' as lexeme  { STR_LIT lexeme }
