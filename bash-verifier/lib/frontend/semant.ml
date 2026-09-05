(* Semantic analysis, in this stage we:
 * - Type check the program and assign types to every expression
 * - Check the placement of return and yield statements and ensure all non-void
 *   functions have return statements
 * - Assign unique names to each variable used in a procedure to eliminate
 *   shadowing
 *)
open Ast

module StringMap = Map.Make(String)

(* The result of semantic analysis (though we do not use decls in favor of
 * maps) *)
module Semant = struct
  type typ_base =
    (* The any type is used to denote types for type variables. The unknown
     * type is used when a type error occured on the right-hand side of a
     * let-binding so we can't determine it's type. This is essentially used
     * to suppress other type errors *)
    | Any | Unknown
    | Void | Bool
    | SInt8 | UInt8 | SInt16 | UInt16 | SInt32 | UInt32 | SInt64 | UInt64
    | Float32 | Float64
    | Function of typ_annt * typ_annt list (* return type and argument types *)
    | StateRef | String
    | Product of typ_annt list | List of typ_annt
    | Named of string * typ_annt list

  (* At this point we discard locations so types don't need any additional
   * information *)
  and typ_annt = typ_base

  type typ = typ_annt

  (* For cases we store an array to the statement for each constructor of the
   * enum. This is much nicer for code-generation *)
  type 's cases_base = 's Iarray.t
  type 's cases = 's cases_base

  include Ast(struct
    type 'a declannt = 'a
    type 'a exprannt = { ast : 'a; typ : typ }
    type 'a stmtannt = 'a

    type 's cases = 's cases_base
    type typ = typ_annt
  end)
end

let rec string_of_type (t : Semant.typ) : string =
  match t with
  | Any     -> "any"
  | Unknown -> "unknown"
  | Void    -> "void"
  | Bool    -> "bool"
  | SInt8   -> "i8"
  | SInt16  -> "i16"
  | SInt32  -> "i32"
  | SInt64  -> "i64"
  | UInt8   -> "u8"
  | UInt16  -> "u16"
  | UInt32  -> "u32"
  | UInt64  -> "u64"
  | Float32 -> "f32"
  | Float64 -> "f64"
  | Function (ret, args) ->
      Printf.sprintf "(%s) -> %s"
        (String.concat ", " (List.map string_of_type args))
        (string_of_type ret)
  | StateRef  -> "state"
  | String    -> "string"
  | Product ts ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map string_of_type ts))
  | List t -> Printf.sprintf "list::<%s>" (string_of_type t)
  | Named (nm, ts) ->
      if List.is_empty ts
      then nm
      else Printf.sprintf "%s::<%s>" nm
            (String.concat ", " (List.map string_of_type ts))

(* Checks type equality but returns true if either type is unknown *)
let types_match (t : Semant.typ) (s : Semant.typ) : bool =
  if t = s then true
  else
    match t, s with
    | Unknown, _ | _, Unknown -> true
    | _, _ -> false

module Env : sig
  type ('v, 't, 'e) t

  val empty : ('v, 't, 'e) t

  val add_type : string -> 't -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_except : string -> 'e -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_unique : string -> 'v -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_value : string -> (string -> 'v) -> ('v, 't, 'e) t
    -> string * ('v, 't, 'e) t

  (* Used to add type variables which are allowed to shadow other type names *)
  val replace_type : string -> 't -> ('v, 't, 'e) t -> ('v, 't, 'e) t

  val find_type : string -> ('v, 't, 'e) t -> 't option
  val find_except : string -> ('v, 't, 'e) t -> 'e option
  val find_value : string -> ('v, 't, 'e) t -> 'v option

  val scope : ('v, 't, 'e) t -> (('v, 't, 'e) t -> 'b) -> 'b
end = struct
  type ('v, 't, 'e) t = {
    values  : (int * 'v) StringMap.t;
    types   : 't StringMap.t;
    excepts : 'e StringMap.t
  }

  let empty = {
    values  = StringMap.empty;
    types   = StringMap.empty;
    excepts = StringMap.empty
  }

  let add_type s x { values; types; excepts } =
    if StringMap.mem s types
    then None
    else Some { values; excepts; types = StringMap.add s x types }

  let add_except s x { values; types; excepts } =
    if StringMap.mem s excepts
    then None
    else Some { values; types; excepts = StringMap.add s x excepts }

  let add_unique s x { values; types; excepts } =
    if StringMap.mem s values
    then None
    (* We flag this entry as a unique name (i.e., a global) by setting the
     * counter to -1. Then, when we add a shadowing local we can identify that
     * we don't actually need to assign it a mangled name (which ensures we
     * don't have to rename function arguments) *)
    else Some { types; excepts; values = StringMap.add s (-1, x) values }

  let add_value s f { values; types; excepts } =
    let unique = ref s
    in let values =
      StringMap.update s (function
        | None -> Some (0, f s)
        | Some (-1, _) -> Some (0, f s)
        | Some (i, _) -> unique := s ^ "." ^ string_of_int i
                       ; Some (i + 1, f !unique))
      values
    in (!unique, { types; excepts; values })
  
  let replace_type s t { values; types; excepts } =
    { values; excepts;
      types = StringMap.add s t types }

  let find_type s { types; _ } = StringMap.find_opt s types

  let find_except s { excepts; _ } = StringMap.find_opt s excepts

  let find_value s { values; _ } = Option.map snd (StringMap.find_opt s values)
  
  let scope m k = k m
end

type func_binding = { 
  ty_args : string list;
  args : (string * Semant.typ) list;
  ret : Semant.typ;
  mutable body : Semant.stmt list
}

type value_binding =
  | Uninterp  of { ty_args : string list; args : Semant.typ list;
                    ret : Semant.typ }
  | Attribute of { local : bool; ty : Semant.typ }
  | Element   of { local : bool; tys : Semant.typ list }
  | Function  of func_binding
  | Local     of { unique : string; typ : Semant.typ }

(* For enums we record a map from the constructor name to an index and an
 * array of argument types for each constructor. This is because in code-gen
 * we need to know the position of each constructor *)
type enum_info = {
  constrs: int StringMap.t;
  typs: Semant.typ list Iarray.t
}
type type_def =
  | Alias of Semant.typ
  | Enum of enum_info
  | Struct of Semant.typ StringMap.t
type type_binding = { ty_args : string list; mutable typ : type_def }

type except_binding = Semant.typ list

type env = (value_binding, type_binding, except_binding) Env.t

let add_ty_args (env : env) (ty_args : string list) : env =
  List.fold_left (fun env nm ->
    Env.replace_type nm { ty_args = []; typ = Alias Any } env)
    env ty_args

let add_local (nm : string) (typ : Semant.typ) (env : env) : string * env =
  Env.add_value nm (fun unique -> Local { unique; typ }) env

type err_msg =
  | Leaf of { pos : Lexing.position * Lexing.position; msg : string }
  | Node of err_msg * err_msg
type 'a err = Ok of 'a | Err of 'a * err_msg

let error default pos =
  Printf.ksprintf (fun msg -> Err (default, Leaf { pos; msg }))

let of_option ~err (x : 'a option) : 'a err =
  match x with
  | Some x -> Ok x
  | None -> err ()

let ( let^ ) (res : 'a err) (f : 'a -> 'b err) : 'b err =
  match res with
  | Ok x -> f x
  | Err (x, es) ->
      match f x with
      | Ok y -> Err (y, es)
      | Err (y, fs) -> Err (y, Node (es, fs))

let map_err (f : 'a -> 'b err) (xs : 'a list) : 'b list err =
  let rec map (xs : 'a list) =
    match xs with
    | [] -> Ok []
    | x :: xs ->
        let^ y = f x
        in let^ ys = map xs
        in Ok (y :: ys)
  in map xs

let err_map (f : 'a -> 'b) (x : 'a err) : 'b err =
  match x with
  | Ok x -> Ok (f x)
  | Err (x, es) -> Err (f x, es)

(* Semantic analysis functions *)
(* Utilities for splitting decls by kind (type, "values", and functions) *)
type decls_split = { 
  types   : Parsed.decl list;
  values  : Parsed.decl list;
  funcs   : Parsed.decl list }

let split_decls (ds : Parsed.decl list) : decls_split =
  let (types, values, funcs) =
    List.fold_right (fun (d : Parsed.decl) (types, values, funcs) ->
      match d.ast with
      | Enum _ | Struct _ | Type _ -> (d :: types, values, funcs)
      | Exception _ | Uninterp _ | Attribute _ | Element _ ->
          (types, d :: values, funcs)
      | Function _ -> (types, values, d :: funcs)
    ) ds ([], [], [])
  in { types; values; funcs }

(* Semantic analysis of types, ensures the proper use of named types *)
let analyze_type (env : env) (ty : Parsed.typ) : Semant.typ err =
  let rec analyze (ty : Parsed.typ) : Semant.typ err =
    match ty.ast with
    | Void    -> Ok Void
    | Bool    -> Ok Bool
    | SInt8   -> Ok SInt8
    | SInt16  -> Ok SInt16
    | SInt32  -> Ok SInt32
    | SInt64  -> Ok SInt64
    | UInt8   -> Ok UInt8
    | UInt16  -> Ok UInt16
    | UInt32  -> Ok UInt32
    | UInt64  -> Ok UInt64
    | Float32 -> Ok Float32
    | Float64 -> Ok Float64
    | Function (ret, args) ->
        let^ ret = analyze ret
        in let^ args = map_err analyze args
        in Ok (Function (ret, args) : Semant.typ)
    | StateRef  -> Ok StateRef
    | String    -> Ok String
    | Product ts ->
        let^ ts = map_err analyze ts
        in Ok (Semant.Product ts)
    | List t ->
        let^ t = analyze t
        in Ok (Semant.List t)
    | Named (nm, ty_args) ->
        let^ ty_args = map_err analyze ty_args
        in let^ ty_info =
          match Env.find_type nm env with
          | None ->
              error { ty_args = []; typ = Alias Unknown} ty.pos
                "Undefined type '%s'" nm
          | Some info -> Ok info
        in if List.length ty_args <> List.length ty_info.ty_args
        then
          match ty_info.typ with
          | Alias Unknown -> Ok Semant.Unknown
          | _ ->
              error Semant.Unknown ty.pos
                "Type '%s' expected %d arguments but provided %d"
                nm (List.length ty_info.ty_args) (List.length ty_args)
        else Ok (Semant.Named (nm, ty_args))
  in analyze ty

let analyze_expr (env : env) (e : Parsed.expr)
  : (Semant.expr * Semant.typ) err =
  failwith "TODO"

let analyze_cond (env : env) (e : Parsed.expr) : Semant.expr err =
  let^ (res, t) = analyze_expr env e
  in match t with
  | Bool | Unknown -> Ok res
  | _ -> error res e.pos "Expected a bool, found %s" (string_of_type t)

(* Semantic analysis of statements, provided the current environment and a
 * context that tells us the return type of the current function and whether we
 * are allowed to yield or not and if so the type *)
type stmt_context = { ret : Semant.typ; yield : Semant.typ ref option }

let rec analyze_stmt (env : env) (ctx : stmt_context) (s : Parsed.stmt)
  : (env * Semant.stmt) err =
  match s.ast with
  | ForLoop (v, ex, body) ->
      let^ (exp, t) = analyze_expr env ex
      in let^ elem_ty =
        match t with
        | List t -> Ok t
        | Unknown -> Ok Semant.Unknown (* an error will already have occured *)
        | t -> error Semant.Unknown ex.pos "Expected a list, found %s"
                (string_of_type t)
      in let (unique, body_env) = add_local v elem_ty env
      in let body_ctx = { ret = ctx.ret; yield = Some (ref Semant.Any) }
      in let^ body = analyze_stmts body_env body_ctx body
      in Ok (env, Semant.ForLoop (unique, exp, body))
  | WhileLoop (cond, body) ->
      let^ cond = analyze_cond env cond
      in let^ body = analyze_stmts env ctx body
      in Ok (env, Semant.WhileLoop (cond, body))
  | IfThenElse (cond, thn, els) ->
      let^ cond = analyze_cond env cond
      in let^ thn = analyze_stmts env ctx thn
      in let^ els = analyze_stmts env ctx els
      in Ok (env, Semant.IfThenElse (cond, thn, els))
  (* TODO: Match, Clear, Touch *)
  (* TODO: Should we also adjust the AST to allow us to change what you
   * specify for clear and touch to allow us to process state references
   * better? *)
  | Assert e ->
      let^ e = analyze_cond env e
      in Ok (env, Semant.Assert e)
  | Return e ->
      let^ (exp, t) = analyze_expr env e
      (* TODO: Indicate that there should be no code following this statement *)
      in let res = (env, Semant.Return exp)
      in if types_match t ctx.ret
      then Ok res
      else error res s.pos "Incorrect return type, expected %s but found %s"
            (string_of_type ctx.ret) (string_of_type t)
  | Yield e ->
      let^ (exp, t) = analyze_expr env e
      (* TODO: Indicate that there should be no code following this statement *)
      in let res = (env, Semant.Yield exp)
      in begin match ctx.yield with
      | None -> error res s.pos "Invalid yield, not contained in a for-loop"
      | Some ({ contents = Any } as yield_ty) ->
          yield_ty := t ; Ok res
      | Some ({ contents = Unknown }) -> Ok res
      | Some ({ contents = yield_ty }) ->
          if types_match t yield_ty
          then Ok res
          else error res s.pos "Incorrect yield type, expected %s but found %s"
                (string_of_type yield_ty) (string_of_type t)
      end
  (* TODO: Raise, Assign *)
  | LetStmt (v, ty, exp) ->
      let^ (exp, t) = analyze_expr env exp
      in let^ t =
        match ty with
        | None -> Ok t
        | Some ty ->
            let^ ty = analyze_type env ty
            in if types_match t ty
            then Ok t
            else error t s.pos "Type mismatched, expected %s but found %s"
                  (string_of_type ty) (string_of_type t)
      in let (unique, env) = add_local v t env
      in Ok (env, Semant.LetStmt (unique, None, exp))
  | Localize body ->
      let^ body = analyze_stmts env ctx body
      in Ok (env, Semant.Localize body)

and analyze_stmts (env : env) (ctx : stmt_context) (stmts : Parsed.stmt list)
  : Semant.stmt list err =
  match stmts with
  | [] -> Ok []
  | s :: tl ->
      let^ (env, s) = analyze_stmt env ctx s
      in let^ tl = analyze_stmts env ctx tl
      in Ok (s :: tl)

let analyze_function (env : env) (ret : Semant.typ) (stmts : Parsed.stmt list)
  : Semant.stmt list err =
  analyze_stmts env { ret; yield = None } stmts

(* Analyze type declarations
 * - Step 1: Collect all the type names to ensure there are no repeated names
 * - Step 2: Process each type to provide a real definition and ensure all
 *    named types exist and are properly used
 * The input, tys, contains only decl of the form Enum _, Struct _, or Type _
 *)
let analyze_types (env : env) (tys : Parsed.decl list) : env err =
  (* Step 1 *)
  let^ env =
    (* The order we process the types in does not matter, so use fold_left
     * since it's tail recursive *)
    List.fold_left (fun env (d : Parsed.decl) ->
      let^ env = env
      in match d.ast with
      | Enum { name; ty_args; _ } | Struct { name; ty_args; _ } ->
          of_option
            ~err:(fun () -> error env d.pos "Type %s already defined" name)
            (Env.add_type name { ty_args; typ = Alias Unknown } env)
      | Type { name; _ } ->
          of_option
            ~err:(fun () -> error env d.pos "Type %s already defined" name)
            (Env.add_type name { ty_args = []; typ = Alias Unknown } env)
      | _ -> failwith "Match error"
    ) (Ok env) tys
  (* Step 2 *)
  in let^ () =
    List.fold_left (fun acc (d : Parsed.decl) ->
      let^ () = acc
      in match d.ast with
      | Enum { name; ty_args; constrs } ->
          let info =
            match Env.find_type name env with
            | None -> failwith "Map error"
            | Some info -> info
          in let typ_env = add_ty_args env ty_args
          in let^ constrs =
            map_err
              (fun (f, ts) ->
                err_map (fun ts -> (f, ts))
                  (map_err (analyze_type typ_env) ts))
              constrs
          in let typs =
            Iarray.of_seq (let rec gen xs () =
              match xs with
              | [] -> Seq.Nil
              | (_, ts) :: tl -> Seq.Cons (ts, gen tl)
            in gen constrs)
          in let constrs =
            StringMap.of_seq (let rec gen xs i () =
              match xs with
              | [] -> Seq.Nil
              | (c, _) :: tl -> Seq.Cons ((c, i), gen tl (i+1))
            in gen constrs 0)
          in Ok (info.typ <- Enum { constrs; typs })
      | Struct { name; ty_args; fields } ->
          let info =
            match Env.find_type name env with
            | None -> failwith "Map error"
            | Some info -> info
          in let typ_env = add_ty_args env ty_args
          in let^ fields =
            map_err 
              (fun (f, t) -> 
                err_map (fun t -> (f, t)) (analyze_type typ_env t))
              fields
          in Ok (info.typ <- Struct (StringMap.of_list fields))
      | Type { name; def } ->
          let info =
            match Env.find_type name env with
            | None -> failwith "Map error"
            | Some info -> info
          in let^ def = analyze_type env def
          in Ok (info.typ <- Alias def)
      | _ -> failwith "Match error"
    ) (Ok ()) tys
  in Ok env

(* Analyze "value" declarations, this includes exceptions, uninterpreted
 * functions, elements, and attributes
 * The unifying idea of these kinds of declarations is that none of them are
 * recursive (else self-recursive or mutually recursive). This means that we
 * can process them in just a single step pass rather than the two steps we
 * need for types and functions. *)
let analyze_values (env : env) (vals : Parsed.decl list) : env err =
  List.fold_left (fun env (d : Parsed.decl) ->
    let^ env = env
    in match d.ast with
    | Exception { name; ty } ->
        let^ tys = map_err (analyze_type env) ty
        in of_option
            ~err:(fun()-> error env d.pos "Exception %s already defined" name)
            (Env.add_except name tys env)
    | Uninterp { name; ty_args; args; ret } ->
        let typ_env = add_ty_args env ty_args
        in let^ args = map_err (analyze_type typ_env) args
        in let^ ret = analyze_type typ_env ret
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name)
            (Env.add_unique name (Uninterp { ty_args; args; ret }) env)
    | Attribute { local; name; ty } ->
        let^ ty = analyze_type env ty
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name)
            (Env.add_unique name (Attribute { local; ty }) env)
    | Element { local; name; ty } ->
        let^ tys = map_err (analyze_type env) ty
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name)
            (Env.add_unique name (Element { local; tys }) env)
    | _ -> failwith "Match error"
  ) (Ok env) vals

(* Semantic analysis for functions. Like with types this is a two-step process,
 * first we add all the functions and their types to the environment to handle
 * potentially recursive definitions and then we process the body of each
 * function (and the order doesn't matter since we already have the type
 * information for every function, which is the only thing that can matter
 * while performing semantic analysis) *)
let analyze_funcs (env : env) (funcs : Parsed.decl list) : env err =
  (* Step 1 *)
  let^ env =
    List.fold_left (fun env (d : Parsed.decl) ->
      let^ env = env
      in match d.ast with
      | Function { name; ty_args; args; ret; _ } ->
          let typ_env = add_ty_args env ty_args
          (* Check that all argument names are distinct, we consider it a
           * semantic error if this is not the case (because this uniqueness is
           * assumed below) *)
          in let^ () =
            let rec find_dups (nms : (string * 'a) list) : unit err =
              match nms with
              | [] -> Ok ()
              | (nm, _) :: tl ->
                  let^ () =
                    if List.exists (fun (x, _) -> x = nm) tl
                    then
                      error () d.pos "Multiple arguments named %s" nm
                    else Ok ()
                  in find_dups tl
            in find_dups args
          in let^ args = map_err (fun (nm, t) ->
            err_map (fun t -> (nm, t)) (analyze_type typ_env t)
          ) args
          in let^ ret = analyze_type typ_env ret
          in of_option
              ~err:(fun () -> error env d.pos "Name %s already defined" name)
              (Env.add_unique name 
                (Function { ty_args; args; ret; body = [] }) env)
      | _ -> failwith "Match error"
    ) (Ok env) funcs
  (* Step 2 *)
  in let^ () =
    List.fold_left (fun acc (d : Parsed.decl) ->
      let^ () = acc
      in match d.ast with
      | Function { name; ty_args; body; _ } ->
          let info =
            match Env.find_value name env with
            | Some (Function info) -> info
            | _ -> failwith "Map error"
          in let typ_env = add_ty_args env ty_args
          in let body_env =
            List.fold_left (fun env (nm, typ) ->
              (* The unique name generated by the environment will always be
               * the same as the actual variable name because variable names
               * are unique (checked above) and there are no locals in the
               * environment yet *)
              let (_, env) = add_local nm typ env
              in env
            ) typ_env info.args
          in let^ body = analyze_function body_env info.ret body
          in Ok (info.body <- body)
      | _ -> failwith "Match error"
    ) (Ok ()) funcs
  in Ok env

(* Entry point *)
let analyze_program (prg : Parsed.decl list) : env err =
  let env : env = Env.empty
  in let { types; values; funcs } = split_decls prg
  in let^ env = analyze_types env types
  in let^ env = analyze_values env values
  in analyze_funcs env funcs
