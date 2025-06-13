type value = Str of string | Unknown of string
type vals = value list

type args = (vals * vals) list
type expr = vals * args

type cond = And of cond * cond
          | Or  of cond * cond
          | Not of cond
          | Eq  of expr * expr
          | Exists of expr
          | Installed of expr
          | Required of expr
          | Running of expr

(* TODO: Need a way to add a user to a group *)
(* TODO: Need a way to change owner/group of a file *)
type action = Clone  of vals | Copy      of vals | Create   of vals
            | Delete of vals | Disable   of vals | Download of vals
            | Enable of vals | Install   of vals | Move     of vals
            | Reboot         | Set       of vals | Start    of vals
            | Stop   of vals | Uninstall of vals | Write    of vals

type atom = action * args

type base = Nil | Cons of atom * base | If of cond * base * base
type top = base list

let unparse_val = function
  | Str s -> s
  | Unknown s -> "?" ^ s
let unparse_vals vs = String.concat " " (List.map unparse_val vs)

let unparse_expr (e : expr) =
  let (v, args) = e
  in unparse_vals v 
   ^ if List.is_empty args then ""
     else (" with "
     ^ String.concat ", "
       (List.map 
         (fun (lhs, rhs) -> unparse_vals lhs ^ " = " ^ unparse_vals rhs)
         args))

let rec unparse_cond = function
  | And (x, y)  -> "(" ^ unparse_cond x ^ " and " ^ unparse_cond y ^ ")"
  | Or  (x, y)  -> "(" ^ unparse_cond x ^ " or "  ^ unparse_cond y ^ ")"
  | Not c       -> "(not " ^ unparse_cond c ^ ")"
  | Eq (x, y)   -> "(" ^ unparse_expr x ^ " equals " ^ unparse_expr y ^ ")"
  | Exists x    -> "(" ^ unparse_expr x ^ " exists)"
  | Installed x -> "(" ^ unparse_expr x ^ " installed)"
  | Required x  -> "(" ^ unparse_expr x ^ " required)"
  | Running x   -> "(" ^ unparse_expr x ^ " running)"

let unparse_action = function
  | Clone vs      -> "clone " ^ unparse_vals vs
  | Copy vs       -> "copy " ^ unparse_vals vs
  | Create vs     -> "create " ^ unparse_vals vs
  | Delete vs     -> "delete " ^ unparse_vals vs
  | Disable vs    -> "disable " ^ unparse_vals vs
  | Download vs   -> "download " ^ unparse_vals vs
  | Enable vs     -> "enable " ^ unparse_vals vs
  | Install vs    -> "install " ^ unparse_vals vs
  | Move vs       -> "move " ^ unparse_vals vs
  | Reboot        -> "reboot"
  | Set vs        -> "set " ^ unparse_vals vs
  | Start vs      -> "start " ^ unparse_vals vs
  | Stop vs       -> "stop " ^ unparse_vals vs
  | Uninstall vs  -> "uninstall " ^ unparse_vals vs
  | Write vs      -> "write " ^ unparse_vals vs

let unparse_atom (act, args) = unparse_action act ^ " with "
  ^ String.concat ", " 
    (List.map 
      (fun (lhs, rhs) -> unparse_vals lhs ^ " = " ^ unparse_vals rhs)
      args)

let rec unparse_base (q: base) =
  match q with
  | Nil -> ""
  | Cons (a, q) -> unparse_atom a ^ "; " ^ unparse_base q
  | If (c, t, e) -> 
      "if " ^ unparse_cond c ^ " then " ^ unparse_base t
                             ^ " else " ^ unparse_base e

let unparse_query (q: top) = String.concat "." (List.map unparse_base q)
