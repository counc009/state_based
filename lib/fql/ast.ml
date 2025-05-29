type vals = string list

type cond = And of cond * cond
          | Or  of cond * cond
          | Not of cond
          | Eq  of vals * vals
          | Exists of vals
          | Required of vals

type action = Backup    of vals | Clone  of vals | Copy    of vals
            | Create    of vals | Delete of vals | Disable of vals
            | Download  of vals | Enable of vals | Ensure  of cond
            | Install   of vals | Move   of vals | Restart
            | Set       of vals | Start  of vals | Stop    of vals
            | Uninstall of vals | Write  of vals

type args = (string list * string list) list
type atom = action * args

type base = Nil | Cons of atom * base | If of cond * base * base
type top = base list

let rec unparse_cond = function
  | And (x, y) -> "(" ^ unparse_cond x ^ " and " ^ unparse_cond y ^ ")"
  | Or  (x, y) -> "(" ^ unparse_cond x ^ " or "  ^ unparse_cond y ^ ")"
  | Not c      -> "(not " ^ unparse_cond c ^ ")"
  | Eq (x, y)  -> "(" ^ String.concat " " x ^ " equals " ^ String.concat " " y ^ ")"
  | Exists x   -> "(" ^ String.concat " " x ^ " exists)"
  | Required x -> "(" ^ String.concat " " x ^ " required)"

let unparse_action = function
  | Backup vs     -> "backup " ^ String.concat " " vs
  | Clone vs      -> "clone " ^ String.concat " " vs
  | Copy vs       -> "copy " ^ String.concat " " vs
  | Create vs     -> "create " ^ String.concat " " vs
  | Delete vs     -> "delete " ^ String.concat " " vs
  | Disable vs    -> "disable " ^ String.concat " " vs
  | Download vs   -> "download " ^ String.concat " " vs
  | Enable vs     -> "enable " ^ String.concat " " vs
  | Ensure c      -> "ensure " ^ unparse_cond c
  | Install vs    -> "install " ^ String.concat " " vs
  | Move vs       -> "move " ^ String.concat " " vs
  | Restart       -> "restart"
  | Set vs        -> "set " ^ String.concat " " vs
  | Start vs      -> "start " ^ String.concat " " vs
  | Stop vs       -> "stop " ^ String.concat " " vs
  | Uninstall vs  -> "uninstall " ^ String.concat " " vs
  | Write vs      -> "write " ^ String.concat " " vs

let unparse_atom (act, args) = unparse_action act ^ " with "
  ^ String.concat ", " 
    (List.map 
      (fun (lhs, rhs) -> String.concat " " lhs ^ " = " ^ String.concat " " rhs)
      args)

let rec unparse_base (q: base) =
  match q with
  | Nil -> ""
  | Cons (a, q) -> unparse_atom a ^ "; " ^ unparse_base q
  | If (c, t, e) -> 
      "if " ^ unparse_cond c ^ " then " ^ unparse_base t
                             ^ " else " ^ unparse_base e

let unparse_query (q: top) = String.concat "." (List.map unparse_base q)
