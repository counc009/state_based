module type AnnotatorType = sig
  type 'a anntd

  (* annotation for a variable; it can be useful for this to be different *)
  type 'a vanntd

  type fact_kind
  type mod_info
end
  
type unary  = Not | Neg | Lower
type binary = Add | Sub | Mul | Pow | Div | Mod
            | And | Or
            | Neq | Eq | Lt | Gt | Le | Ge
            | Concat

module Ast(A : AnnotatorType) = struct
  type value =
    | String      of string A.anntd
    | Int         of int A.anntd
    | Float       of float A.anntd
    | Bool        of bool A.anntd
    | List        of value list A.anntd
    | Ident       of string A.vanntd
    | Unary       of (value * unary) A.anntd
    | Binary      of (value * binary * value) A.anntd
    | Dot         of (value * string) A.anntd
    | VarDefined  of string A.anntd
    | Fact        of A.fact_kind A.anntd
    | Ternary     of (value * value * value) A.anntd
    | Record      of (string * value) list A.anntd
    | ReAnnt      of value A.anntd

  type mod_use = {
    mod_info: A.mod_info;
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
    failed_when : value option;
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
    failed_when : value option;
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
end

module Parsed = struct
  include Ast(struct
    type 'a anntd = 'a
    type 'a vanntd = 'a
    type fact_kind = string
    type mod_info = string
  end)
end
