{
  open Parser
}

rule token = parse
  | [' ''\t''\n'] { token lexbuf }

  | ';'           { SEMI }
  | '.'           { DOT }
  | ','           { COMMA }
  | '='           { EQ }

  | "if"          { IF }
  | "then"        { THEN }
  | "otherwise"   { ELSE }

  | "and"         { AND }
  | "or"          { OR }
  | "is"          { IS }
  | "equals"      { EQUALS }
  | "exists"      { EXISTS }
  | "installed"   { INSTALLED }
  | "required"    { REQUIRED }
  | "running"     { RUNNING }
  | "not"         { NOT }

  | "at"          { AT }
  | "for"         { FOR }
  | "from"        { FROM }
  | "in"          { IN }
  | "into"        { INTO }
  | "to"          { TO }
  | "via"         { VIA }
  | "with"        { WITH }

  | "clone"       { CLONE }
  | "copy"        { COPY }
  | "create"      { CREATE }
  | "delete"      { DELETE }
  | "disable"     { DISABLE }
  | "download"    { DOWNLOAD }
  | "enable"      { ENABLE }
  | "install"     { INSTALL }
  | "move"        { MOVE }
  | "reboot"      { REBOOT }
  | "set"         { SET }
  | "start"       { START }
  | "stop"        { STOP }
  | "uninstall"   { UNINSTALL }
  | "write"       { WRITE }

  | '?'([^' ''\t''\n'';''.'',''=''"']+ as lexeme) { UNKNOWN lexeme } 
  | [^' ''\t''\n'';''.'',''=''"']+ as lexeme      { ID lexeme }
  | '"'([^'"']* as lexeme)'"'                     { STR lexeme }
  | eof                                           { EOF }
