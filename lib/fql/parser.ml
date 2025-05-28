open Angstrom

let is_whitespace = function
  | '\x09' | '\x0a' | '\x0d' | '\x20' -> true
  | _ -> false

let whitespace = take_while is_whitespace

let token_terminator = function
  | '\x09' | '\x0a' | '\x0d' | '\x20' (* whitespace *)
  | '.' | ';' | ',' | '=' (* symbols that terminate tokens *)
    -> true
  | _ -> false

(* Parses any single token (so excluding terminators) and any following
 * whitespace *)
let token = take_while1 (fun c -> not( token_terminator c)) <* whitespace

(* Parses a non-whitespace terminator and consumes any following whitespace*)
let term = satisfy token_terminator <* whitespace

type token = T of string | Dot | Semi | Comma | Eq

let tokenizer =
  whitespace
  *> many
    ((token >>| fun s -> T s)
    <|>
    (term >>= function
      | '.' -> return Dot
      | ';' -> return Semi
      | ',' -> return Comma
      | '=' -> return Eq
      | _ -> fail "Unknown terminator"))

let tokenize : string -> (token list, string) result
  = parse_string ~consume:All tokenizer

type cat = string list
type expr = string list
type cond = And of cond * cond | Or of cond * cond | Not of cond
          | Eq of expr * expr  | Exists of cat     | Required of cat
type action = Backup    of cat | Clone  of cat | Copy    of cat
            | Create    of cat | Delete of cat | Disable of cat
            | Download  of cat | Enable of cat | Ensure  of cond
            | Install   of cat | Move   of cat | Restart
            | Set       of cat | Start  of cat | Stop    of cat
            | Uninstall of cat | Write  of cat
type args = (string * expr) list
type atom = action * args
type base_query = Atom of atom | Cond of cond * base_query list * base_query list
type flq = base_query list

let parse_cond (_toks: token list) : (cond * token list, string) result =
  Error "TODO"

let parse_atom (_toks: token list) : (atom * token list, string) result =
  Error "TODO"

let rec parse_base (toks: token list) : (base_query list * token list, string) result =
  match toks with
  | T "if" :: toks -> Result.bind (parse_cond toks)
    (fun (c, toks) ->
      match toks with
      | T "then" :: toks ->
          Result.bind (parse_base toks)
            (fun (t, toks) ->
              match toks with
              | T "else" :: toks ->
                  Result.bind (parse_base toks)
                    (fun (e, toks) -> Ok ([Cond (c, t, e)], toks))
              | _ -> Ok ([Cond (c, t, [])], toks))
      | _ -> Error "expected matching then for if")
  | _ -> Result.bind (parse_atom toks)
    (fun (a, toks) ->
      match toks with
      | Semi :: T "and" :: toks | Semi :: toks 
        -> Result.map (fun (tl, ts) -> (Atom a :: tl, ts)) (parse_base toks)
      | _ -> Ok ([Atom a], toks))

let rec parse_top (toks: token list) : (flq * token list, string) result =
  Result.bind (parse_base toks)
    (fun (b, toks) ->
      match toks with
      | [] -> Ok (b, [])
      | Dot :: toks -> Result.map (fun (t, ts) -> (b @ t, ts)) (parse_top toks)
      | _ -> Error "Expected '.' or end-of-query")
