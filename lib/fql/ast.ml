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
