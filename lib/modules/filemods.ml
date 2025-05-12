type mod_action = Set | Unset | Preserve
type mod_set = { mutable read: mod_action;
                 mutable write: mod_action;
                 mutable execute: mod_action }
type mod_val = { owner: mod_set
               ; group: mod_set
               ; other: mod_set
               ; mutable setuid: mod_action
               ; mutable setgid: mod_action
               ; mutable sticky: mod_action }

let init_mod_set () : mod_set = { read = Preserve; write = Preserve; execute = Preserve }

let init_mod_val () : mod_val = {
  owner = init_mod_set ();
  group = init_mod_set ();
  other = init_mod_set ();
  setuid = Preserve;
  setgid = Preserve;
  sticky = Preserve;
}

(* numeric codes should be in octal with an optional leading = *)
let numeric_mode_regex = Str.regexp {|=?[0-9]+|}

let substr (s: string) (idx: int) : string =
  String.sub s idx (String.length s - idx)

let parse_mod_numeric str cur : (mod_val, string) result =
  let (sets, numbers) =
    if str.[0] = '='
    then (true, substr str 1)
    else (false, str)
  in let numbers =
    if String.length numbers = 4
    then Ok (numbers.[0], numbers.[1], numbers.[2], numbers.[3])
    else if String.length numbers = 3
    then if sets
      then Ok ('0', numbers.[0], numbers.[1], numbers.[2])
      else Ok ('p', numbers.[0], numbers.[1], numbers.[2])
    else Error "invalid mode, expected 3-4 octal digits"
  in Result.bind numbers
    (fun (config, owner, group, other) ->
      cur.owner.read 
        <- if owner = '4' || owner = '5' || owner = '6' || owner = '7'
           then Set else Unset
      ; cur.owner.write
        <- if owner = '2' || owner = '3' || owner = '6' || owner = '7'
           then Set else Unset
      ; cur.owner.execute
        <- if owner = '1' || owner = '3' || owner = '5' || owner = '7'
           then Set else Unset
      ; cur.group.read 
        <- if group = '4' || group = '5' || group = '6' || group = '7'
           then Set else Unset
      ; cur.group.write
        <- if group = '2' || group = '3' || group = '6' || group = '7'
           then Set else Unset
      ; cur.group.execute
        <- if group = '1' || group = '3' || group = '5' || group = '7'
           then Set else Unset
      ; cur.other.read 
        <- if other = '4' || other = '5' || other = '6' || other = '7'
           then Set else Unset
      ; cur.other.write
        <- if other = '2' || other = '3' || other = '6' || other = '7'
           then Set else Unset
      ; cur.other.execute
        <- if other = '1' || other = '3' || other = '5' || other = '7'
           then Set else Unset
      ; (if config = 'p' then ()
      else (
        cur.setuid
          <- if config = '4' || config = '5' || config = '6' || config = '7'
             then Set else Unset
        ; cur.setgid
          <- if config = '2' || config = '3' || config = '6' || config = '7'
             then Set else Unset
        ; cur.sticky
          <- if config = '1' || config = '3' || config = '5' || config = '7'
             then Set else Unset))
      ; Ok cur)

let symbolic_mode_regex = Str.regexp {|\([ugoa]*\)\([=+-]\)\([ugo]\|[rwxXst]*\)$|}

let parse_mod_symbolic str cur : (mod_val, string) result =
  if not (Str.string_match symbolic_mode_regex str 0)
  then Error "invalid symbolic mode"
  else
    let users = 
      (* chmod treats to user specification as an a, technically it says if
       * nothing is provided it is different from a because it uses the umask,
       * but I'm not bothering to model that at this stage *)
      let users = Str.matched_group 1 str
      in if users = "" then "a" else users
    in let change = Str.matched_group 2 str
    in let perms = Str.matched_group 3 str
    in let equals = change = "="
    in let subtract = change = "-"
    in (if String.contains users 'u' || String.contains users 'a'
      then 
        (if equals
         then cur.owner.read <- Unset; cur.owner.write <- Unset
            ; cur.owner.execute <- Unset; cur.setuid <- Unset)
        ; String.fold_left
          (fun () perm ->
            match perm with
            | 'u' | 'g' | 'o' -> failwith "Setting permission to another is not handled"
            | 'r' -> cur.owner.read <- if subtract then Unset else Set
            | 'w' -> cur.owner.write <- if subtract then Unset else Set
            | 'x' -> cur.owner.execute <- if subtract then Unset else Set
            | 'X' -> failwith "'X' permission not handled"
            | 's' -> cur.setuid <- if subtract then Unset else Set
            | 't' -> ()
            | _ -> failwith "INTERNAL ERROR")
          () perms)
    ; (if String.contains users 'g' || String.contains users 'a'
      then 
        (if equals
         then cur.group.read <- Unset; cur.group.write <- Unset
            ; cur.group.execute <- Unset; cur.setgid <- Unset)
        ; String.fold_left
          (fun () perm ->
            match perm with
            | 'u' | 'g' | 'o' -> failwith "Setting permission to another is not handled"
            | 'r' -> cur.group.read <- if subtract then Unset else Set
            | 'w' -> cur.group.write <- if subtract then Unset else Set
            | 'x' -> cur.group.execute <- if subtract then Unset else Set
            | 'X' -> failwith "'X' permission not handled"
            | 's' -> cur.setgid <- if subtract then Unset else Set
            | 't' -> ()
            | _ -> failwith "INTERNAL ERROR")
          () perms)
    ; (if String.contains users 'o' || String.contains users 'a'
      then 
        (if equals
         then cur.other.read <- Unset; cur.other.write <- Unset
            ; cur.other.execute <- Unset; cur.sticky <- Unset)
        ; String.fold_left
          (fun () perm ->
            match perm with
            | 'u' | 'g' | 'o' -> failwith "Setting permission to another is not handled"
            | 'r' -> cur.other.read <- if subtract then Unset else Set
            | 'w' -> cur.other.write <- if subtract then Unset else Set
            | 'x' -> cur.other.execute <- if subtract then Unset else Set
            | 'X' -> failwith "'X' permission not handled"
            | 's' -> ()
            | 't' -> cur.sticky <- if subtract then Unset else Set
            | _ -> failwith "INTERNAL ERROR")
          () perms)
    ; Ok cur

let parse_mods_full str : (mod_val, string) result =
  if Str.string_match numeric_mode_regex str 0
  then parse_mod_numeric str (init_mod_val ())
  else parse_mod_symbolic str (init_mod_val ())

let parse_mods_symbolic pieces : (mod_val, string) result =
  List.fold_left
    (fun cur piece -> Result.bind cur (parse_mod_symbolic piece))
    (Ok (init_mod_val ()))
    pieces

let parse_mods str : (mod_val, string) result =
  let pieces = String.split_on_char ',' str
  in match pieces with
  | [] -> Error "Invalid mode"
  | [m] -> parse_mods_full m
  (* Only symbolic modes are allowed to be separated by , *)
  | _ -> parse_mods_symbolic pieces
