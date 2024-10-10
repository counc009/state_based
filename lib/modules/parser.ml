open Angstrom

let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _ -> false

let whitespace = take_while is_whitespace

let is_digit = function '0'..'9' -> true | _ -> false

let integer = take_while1 is_digit

let sign =
  peek_char
  >>= function
    | Some '-' -> advance 1 >>| fun () -> "-"
    | Some '+' -> advance 1 >>| fun () -> "+"
    | Some c when (is_digit c) ->  return "+"
    | _ -> fail "Sign or digit expected"

let dot =
  peek_char
  >>= function
    | Some '.' -> advance 1 >>| fun () -> true
    | _ -> return false

let number =
  sign
  >>= fun sign ->
  take_while1 is_digit
  >>= fun whole ->
  dot
  >>= function
  | false -> return (float_of_string (sign ^ whole))
  | true ->
      take_while1 is_digit >>= fun part ->
      return (float_of_string (sign ^ whole ^ "." ^ part))

let identifier =
  satisfy (function 'a'..'z' | 'A'..'Z' -> true | _ -> false)
  >>= fun c ->
  take_while (function 'a'..'z' | 'A'..'Z' | '_' | '-' -> true | _ -> false)
  >>| fun rest -> String.make 1 c ^ rest

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'
let brackets p = char '{' *> whitespace *> p <* whitespace <* char '}'
let square p = char '[' *> whitespace *> p <* whitespace <* char ']'

let optional p =
  option None (lift (fun x -> Some x) p)

type typ = Bool | Int | Float | String | Path | Named of string | Unit
         | Product of typ list

type expr = Id of string | BoolLit of bool | IntLit of int | FloatLit of float
          | StringLit of string | UnitExp | ProductExp of expr list
          | Provided of string | Function of string * expr list
          | Field of expr * expr

(* Patterns are just of the form <name>[(<names>)] *)
type pattern = string * string list

type stmt = RequiredVar of (string * string list * typ * expr option) list
          | OptionalVar of (string * string list * typ * expr option) list
          | ForLoop     of string * expr * stmt list
          | IfProvided  of string * stmt list * stmt list
          | IfThenElse  of expr * stmt list * stmt list
          | Match       of expr * (pattern * stmt list) list
          | Clear       of expr
          | Assert      of expr
          | Assign      of expr * expr

type topLevel = Enum      of string * (string * typ option) list
              | Uninterp  of string * typ * typ
              | Attribute of string * typ
              | Element   of string * typ
              | Procedure of string * (string * typ) list * stmt list
              | Module    of string * stmt list

let typ =
  fix (fun t ->
    choice
      [ (string "bool"   >>| fun _ -> Bool)
      ; (string "int"    >>| fun _ -> Int)
      ; (string "float"  >>| fun _ -> Float)
      ; (string "string" >>| fun _ -> String)
      ; (string "path"   >>| fun _ -> Path)
      ; (identifier >>| fun nm -> Named nm)
      ; (parens (sep_by (whitespace *> char ',' *> whitespace) t)
        >>| function
          | [] -> Unit
          | [t] -> t
          | ts -> Product ts)
      ])

(* ptype parsed an already parens type, hence we handle commas *)
let ptype =
  sep_by (whitespace *> char ',' *> whitespace) typ
  >>| function
    | [] -> Unit
    | [t] -> t
    | ts -> Product ts

let enum_case =
  identifier
  >>= fun nm ->
  whitespace
  *>
  optional (parens ptype)
  >>| fun ty -> (nm, ty)

let enum_cases =
  sep_by (whitespace *> char ',' *> whitespace) enum_case

(* Procedure arguments are of the form <name> : <type> *)
let proc_arg =
  identifier
  >>= fun nm ->
  whitespace
  *> char ':'
  *> whitespace
  *> typ
  >>| fun typ -> (nm, typ)

let proc_args =
  sep_by (whitespace *> char ',' *> whitespace) proc_arg

(* TODO *)
let expr = string "TODO" >>| fun _ -> Id "todo"

(* Module arguments are of the form <name> [aka <names>] : <type> [= <default>] *)
let mod_aka =
  option [] (string "aka" *> whitespace 
            *> sep_by1 (whitespace *> char ',' *> whitespace) identifier)

let mod_arg =
  identifier
  >>= fun nm ->
  whitespace
  *> mod_aka
  >>= fun alias ->
  whitespace
  *> char ':'
  *> whitespace
  *> typ
  >>= fun typ ->
  whitespace
  *> optional (char '=' *> whitespace *> expr)
  >>| fun default -> (nm, alias, typ, default)

(* Module arguments are separated by | since they represent options *)
let mod_args =
  sep_by (whitespace *> char '|' *> whitespace) mod_arg

(* TODO *)
let stmt =
  choice 
  [ (parens mod_args >>| fun args -> RequiredVar args)
  ; (square mod_args >>| fun args -> OptionalVar args)
  ]

let stmts = whitespace *> sep_by whitespace stmt

let enum_def =
  string "enum"
  *> whitespace
  *> identifier
  <* whitespace
  >>= fun nm ->
  brackets enum_cases
  >>| fun def -> Enum (nm, def)

let uninterp_def =
  string "uninterpreted"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens ptype
  >>= fun arg ->
  whitespace
  *> string "->"
  *> whitespace
  *> typ
  >>| fun res -> Uninterp (nm, arg, res)

let attr_def =
  string "attribute"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens ptype
  >>| fun t -> Attribute (nm, t)

let elem_def =
  string "element"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens ptype
  >>| fun t -> Element (nm, t)

let proc_def =
  string "procedure"
  *> whitespace
  *> identifier
  >>= fun nm ->
  whitespace
  *> parens proc_args
  >>= fun args ->
  whitespace
  *> brackets stmts
  >>| fun body -> Procedure (nm, args, body)
