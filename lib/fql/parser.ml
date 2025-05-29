open Angstrom

let is_whitespace = function
  | '\x09' | '\x0a' | '\x0d' | '\x20' -> true
  | _ -> false

let whitespace = take_while is_whitespace

let token_terminator = function
  | '\x09' | '\x0a' | '\x0d' | '\x20' (* whitespace *)
  | '.' | ';' | ',' | '=' (* symbols that terminate tokens *)
  | '"' (* string opening character *)
    -> true
  | _ -> false

(* Parses any single token (so excluding terminators) and any following
 * whitespace *)
let token = take_while1 (fun c -> not (token_terminator c)) <* whitespace

(* Parses a string literal and any following whitespace. Returns the string
 * without quotes *)
let str_lit = char '"' *> take_while (fun c -> c <> '"') <* char '"' <* whitespace

(* Parses a non-whitespace terminator and consumes any following whitespace*)
let term = satisfy token_terminator <* whitespace

type token = T of string | S of string | Dot | Semi | Comma | Eq

let tokenizer =
  whitespace
  *> many
    ((token >>| fun s -> T s)
    <|> (str_lit >>| fun s -> S s)
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
type args = (string list * expr) list
type atom = action * args
type base_query = Atom of atom | Cond of cond * base_query list * base_query list
type flq = base_query list

let parse_expr (toks: token list) : (expr * token list, string) result =
  let rec parse toks =
    match toks with
    | T s :: toks when s <> "at"     && s <> "for" && s <> "from" && s <> "in"
                    && s <> "into"   && s <> "to"  && s <> "with" && s <> "equals"
                    && s <> "exists" && s <> "is"  && s <> "not"  && s <> "required"
                    && s <> "or"     && s <> "and" && s <> "then"
        -> Result.map (fun (c, ts) -> (s :: c, ts)) (parse toks)
    | S s :: toks -> Result.map (fun (c, ts) -> (s :: c, ts)) (parse toks)
    | _ -> Ok ([], toks)
  in Result.bind (parse toks)
    (fun (e, ts) -> if List.is_empty e then Error "empty expression"
                                       else Ok (e, ts))

(*
 cond ::= c1 cond'
cond' ::= ε | 'or' c1 cond'
   c1 ::= c2 c1'
  c1' ::= ε | 'and' c2 c1'
   c2 ::= expr 'equals' expr
        | expr 'is' expr
        | expr 'not' 'equals' expr
        | expr 'is' 'not' expr
        | expr 'exists'
        | expr 'not' 'exists'
        | expr 'required'
        | expr 'not' 'required'
*)
let parse_cond (toks: token list) : (cond * token list, string) result =
  let parse_c2 (toks: token list) : (cond * token list, string) result =
    Result.bind (parse_expr toks)
      (fun (lhs, toks) ->
        match toks with
        | T "not" :: T "equals" :: toks | T "is" :: T "not" :: toks ->
            Result.map (fun (rhs, ts) -> (Not (Eq (lhs, rhs)), ts))
              (parse_expr toks)
        | T "equals" :: toks | T "is" :: toks ->
            Result.map (fun (rhs, ts) -> (Eq (lhs, rhs), ts)) 
              (parse_expr toks)
        | T "exists" :: toks -> Ok (Exists lhs, toks)
        | T "not" :: T "exists" :: toks -> Ok (Not (Exists lhs), toks)
        | T "required" :: toks -> Ok (Required lhs, toks)
        | T "not" :: T "required" :: toks -> Ok (Not (Required lhs), toks)
        | _ -> Error "invalid condition")

  in let rec parse_c1' (lhs, toks) =
    match toks with
    | T "and" :: toks ->
        Result.bind (parse_c2 toks)
          (fun (rhs, ts) -> parse_c1' (And (lhs, rhs), ts))
    | _ -> Ok (lhs, toks)

  in let parse_c1 toks = Result.bind (parse_c2 toks) parse_c1'

  in let rec parse_cond' (lhs, toks) =
    match toks with
    | T "or" :: toks ->
        Result.bind (parse_c1 toks)
          (fun (rhs, ts) -> parse_cond' (Or (lhs, rhs), ts))
    | _ -> Ok (lhs, toks)

  in Result.bind (parse_c1 toks) parse_cond'

let parse_cat (toks: token list) : (cat * token list, string) result =
  let rec parse toks =
    match toks with
    | T s :: toks when s <> "at"   && s <> "for" && s <> "from" && s <> "in"
                    && s <> "into" && s <> "to"  && s <> "with"
        -> Result.map (fun (c, ts) -> (s :: c, ts)) (parse toks)
    | S s :: toks -> Result.map (fun (c, ts) -> (s :: c, ts)) (parse toks)
    | _ -> Ok ([], toks)
  in Result.bind (parse toks)
    (fun (c, ts) -> if List.is_empty c then Error "empty category"
                                       else Ok (c, ts))

(* arguments have either the form <separator> <value> such as "from path"
 * or <seperator> <lhs>=<rhs>, ...
 *)
let rec parse_args (toks: token list) : (args * token list, string) result =
  let rec parse_vals nm toks =
    Result.bind (parse_cat toks)
      (fun (l, toks) ->
        match toks with
        | Eq :: toks -> Result.bind (parse_cat toks)
            (fun (r, toks) ->
              match toks with
              | Comma :: toks ->
                  Result.map
                    (fun (vs, ts) -> ((l, r) :: vs, ts)) 
                    (parse_vals None toks)
              | _ ->
                  Result.map
                    (fun (vs, ts) -> ((l, r) :: vs, ts))
                    (parse_args toks))
        | _ ->
          match nm with
          | Some nm ->
              Result.map
                (fun (vs, ts) -> ((nm, l) :: vs, ts))
                (parse_args toks)
          | None -> Error "variable name required with multiple values")
  in match toks with
  | T s :: toks when s = "at"   || s = "for" || s = "from" || s = "in"
                  || s = "into" || s = "to"  || s = "with"
      -> parse_vals (Some [s]) toks
  | _ -> Ok ([], toks)

let parse_action (toks: token list) : (action * token list, string) result =
  match toks with
  | T "backup" :: toks ->
      Result.map (fun (c, toks) -> (Backup c, toks)) (parse_cat toks)
  | T "clone" :: toks ->
      Result.map (fun (c, toks) -> (Clone c, toks)) (parse_cat toks)
  | T "copy" :: toks ->
      Result.map (fun (c, toks) -> (Copy c, toks)) (parse_cat toks)
  | T "create" :: toks ->
      Result.map (fun (c, toks) -> (Create c, toks)) (parse_cat toks)
  | T "delete" :: toks ->
      Result.map (fun (c, toks) -> (Delete c, toks)) (parse_cat toks)
  | T "disable" :: toks ->
      Result.map (fun (c, toks) -> (Disable c, toks)) (parse_cat toks)
  | T "download" :: toks ->
      Result.map (fun (c, toks) -> (Download c, toks)) (parse_cat toks)
  | T "enable" :: toks ->
      Result.map (fun (c, toks) -> (Enable c, toks)) (parse_cat toks)
  | T "ensure" :: toks ->
      Result.map (fun (c, toks) -> (Ensure c, toks)) (parse_cond toks)
  | T "install" :: toks ->
      Result.map (fun (c, toks) -> (Install c, toks)) (parse_cat toks)
  | T "move" :: toks ->
      Result.map (fun (c, toks) -> (Move c, toks)) (parse_cat toks)
  | T "restart" :: toks -> Ok (Restart, toks)
  | T "set" :: toks ->
      Result.map (fun (c, toks) -> (Set c, toks)) (parse_cat toks)
  | T "start" :: toks ->
      Result.map (fun (c, toks) -> (Start c, toks)) (parse_cat toks)
  | T "stop" :: toks ->
      Result.map (fun (c, toks) -> (Stop c, toks)) (parse_cat toks)
  | T "uninstall" :: toks ->
      Result.map (fun (c, toks) -> (Uninstall c, toks)) (parse_cat toks)
  | T "write" :: toks ->
      Result.map (fun (c, toks) -> (Write c, toks)) (parse_cat toks)
  | _ -> Error "invalid action"

let parse_atom (toks: token list) : (atom * token list, string) result =
  Result.bind (parse_action toks)
    (fun (a, toks) ->
      Result.map (fun (args, toks) -> ((a, args), toks)) (parse_args toks))

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
