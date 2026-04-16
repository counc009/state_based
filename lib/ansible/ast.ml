type unary  = Not | Neg | Lower
type binary = Add | Sub | Mul | Pow | Div | Mod
            | And | Or
            | Neq | Eq | Lt | Gt | Le | Ge
            | Concat

type value =
  | String      of string
  | Int         of int
  | Float       of float
  | Bool        of bool
  | List        of value list
  | Ident       of string
  | Unary       of value * unary
  | Binary      of value * binary * value
  | Dot         of value * string
  | VarDefined  of string
  | Fact        of string
  | Ternary     of value * value * value
  | Record      of (string * value) list

type mod_use = {
  mod_name: string;
  args: (string * value) list
}

type loop_kind =
  | ItemLoop of value
  | FileGlob of value

type task_body =
  | Module of mod_use
  | Block  of block

and block = {
  tasks: task list;
  rescue: task list option;
  always: task list option
}

and task = {
  name: string;
  register: string;
  ignore_errors: bool;
  condition: value option;
  loop: loop_kind option;
  body: task_body;
  become: bool;
  become_user: string;
  notify: value list
}

type handler = {
  name: string;
  listen: string;
  register: string;
  ignore_errors: bool;
  condition: value option;
  loop: loop_kind option;
  module_invoke: mod_use;
  become: bool;
  become_user: string;
}

type play = {
  name        : string;
  hosts       : string option;
  remote_user : string;
  is_root     : bool option;
  become      : bool;
  become_user : string;
  pre_tasks   : task list option;
  tasks       : task list;
  post_tasks  : task list option;
  handlers    : handler list;
  vars        : (string * value) list
}

type playbook = play list
