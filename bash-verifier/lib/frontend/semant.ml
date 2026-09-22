(* Semantic analysis, in this stage we:
 * - Type check the program and assign types to every expression
 * - Check the placement of return and yield statements and ensure all non-void
 *   functions have return statements
 * - Assign unique names to each variable used in a procedure to eliminate
 *   shadowing
 *)
open Ast

module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

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
    | StateRef | String | Char
    | Product of typ_annt list | List of typ_annt
    | Named of string * typ_annt list

  (* At this point we discard locations so types don't need any additional
   * information *)
  and typ_annt = typ_base

  type typ = typ_annt

  (* For cases we store an array to the variable names and body for each
   * constructor of the enum. This is much nicer for code-generation *)
  type 's cases_base = (string list * 's) Iarray.t
  type 's cases = 's cases_base

  type 'a eannt = { ast : 'a; typ : typ }

  type 'e element =
    | StateTop
    | LocalTop
    | Nested of 'e element * string * 'e list

  include Ast(struct
    type 'a declannt = 'a
    type 'a exprannt = 'a eannt
    type 'a stmtannt = 'a
    type 'a elemannt = 'a element

    type 'a tokannt  = 'a

    type 'a ssep = 'a
    type 'a func = (string * typ_annt) list * typ_annt * 'a list ref
    type uninterp = typ_annt list * typ_annt * string

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
  | Char      -> "char"
  | Product ts ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map string_of_type ts))
  | List t -> Printf.sprintf "list::<%s>" (string_of_type t)
  | Named (nm, ts) ->
      if List.is_empty ts
      then nm
      else Printf.sprintf "%s::<%s>" nm
            (String.concat ", " (List.map string_of_type ts))

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
  args : (Parsed.name * Semant.typ) list;
  ret : Semant.typ;
  body : Semant.stmt list ref
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

let add_ty_args (env : env) (ty_args : Parsed.name list) : env =
  List.fold_left (fun env (nm : Parsed.name) ->
    Env.replace_type nm.ast { ty_args = []; typ = Alias Any } env)
    env ty_args

let add_local (nm : Parsed.name) (typ : Semant.typ) (env : env)
  : string * env =
  Env.add_value nm.ast (fun unique -> Local { unique; typ }) env

type err_msg =
  | Leaf of { pos : Lexing.position * Lexing.position; msg : string }
  | Node of err_msg * err_msg
type 'a err = Ok of 'a | Err of 'a * err_msg

let error default pos =
  Printf.ksprintf (fun msg -> Err (default, Leaf { pos; msg }))

let prepend_error res pos =
  Printf.ksprintf (fun msg ->
    match res with
    | Ok x -> Err (x, Leaf { pos; msg })
    | Err (x, errs) -> Err (x, Node (Leaf { pos; msg }, errs)))

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

let map2_err (f : 'a -> 'b -> 'c err) (xs : 'a list) (ys : 'b list)
  : 'c list err =
  let rec map (xs : 'a list) (ys : 'b list) =
    match xs, ys with
    | [], [] -> Ok []
    | x :: xs, y :: ys ->
        let^ z = f x y
        in let^ zs = map xs ys
        in Ok (z :: zs)
    | _, _ -> raise (Invalid_argument "map2_err")
  in map xs ys

let err_map (f : 'a -> 'b) (x : 'a err) : 'b err =
  match x with
  | Ok x -> Ok (f x)
  | Err (x, es) -> Err (f x, es)

(* match_length xs ys d returns a list of the same length as xs where the
 * elements are taken from ys until it runs out and then all elements are d *)
let rec match_length (xs : 'a list) (ys : 'b list) (default : 'b) : 'b list =
  match xs, ys with
  | [], _ -> []
  | _ :: xs, y :: ys -> y :: match_length xs ys default
  | _ :: xs, [] -> default :: match_length xs [] default

(* Utility for adding multiple variables and checking that there are no
 * duplicates *)
let add_locals pos (nms : Parsed.name list) (tys : Semant.typ list) (env : env)
  : (string list * env) err =
  let duplicates =
    let (_, duplicates) =
      List.fold_left (fun (set, duplicates) { Parsed.ast = v; pos } ->
        if StringSet.mem v set
        then 
          (set, 
           StringMap.update v
            (function None -> Some pos | Some x -> Some x)
            duplicates)
        else (StringSet.add v set, duplicates)
      ) (StringSet.empty, StringMap.empty) nms
    in duplicates
  in let res =
    List.fold_right2 (fun nm ty (uniques, env) ->
      let (unique, env) = add_local nm ty env
      in (unique :: uniques, env)
    ) nms tys ([], env)
  in StringMap.fold (fun v pos res ->
    prepend_error res pos "Variable '%s' already declared" v
  ) duplicates (Ok res)

(* Type Utilities *)

(* Checks type equality but returns true if either type is unknown *)
let rec types_match env (t : Semant.typ) (s : Semant.typ) : bool =
  if t = s then true
  else
    match t, s with
    | Unknown, _ | _, Unknown -> true
    (* If one of our types is a type-alias inline the definition and try
     * again. We do not inline struct and enum types, though hence our type
     * system is a nominal type system rather than a structural one *)
    | Named (nt, _), Named (ns, _) ->
        begin match Env.find_type nt env with
        (* Type aliases do not have type arguments *)
        | Some { typ = Alias t; _ } -> types_match env t s
        | _ ->
            match Env.find_type ns env with
            | Some { typ = Alias s; _ } -> types_match env t s
            | _ -> false
        end
    | Named (nm, _), _ ->
        begin match Env.find_type nm env with
        | Some { typ = Alias t; _ } -> types_match env t s
        | _ -> false
        end
    | _, Named (nm, _) ->
        begin match Env.find_type nm env with
        | Some { typ = Alias s; _ } -> types_match env t s
        | _ -> false
        end
    | _, _ -> false

(* Checks whether a type can be cast to another (and returns the resulting
 * type) *)
let rec check_cast env (from : Semant.typ) (into : Semant.typ)
  : Semant.typ option =
  let types_eq (xs : Semant.typ list) (ys : Semant.typ list) : bool =
    (* xs and ys must be the same length since they were applied to the same
     * type name *)
    List.for_all2 (types_match env) xs ys
  in match from, into with
  (* Don't create additional errors if either type is Unknown *)
  | Unknown, _ | _, Unknown -> Some Unknown
  | Void, Void
  | Bool, Bool
  | ( SInt8 | SInt16 | SInt32 | SInt64 | UInt8 | UInt16 | UInt32 | UInt64
    | Float32 | Float64 | Char )
  , ( SInt8 | SInt16 | SInt32 | SInt64 | UInt8 | UInt16 | UInt32 | UInt64
    | Float32 | Float64 | Char )
  | String, String
  | StateRef, StateRef
    -> Some into
  (* Named types can be cast if either they are the same name and type arguments
   * or one of the types is an alias and then we inline the definition and
   * attempt to cast it *)
  | Named (nf, tf), Named (ni, ti) ->
      if nf = ni && types_eq tf ti
      then Some into
      else
        begin match Env.find_type nf env with
        | Some { typ = Alias from; _ } -> check_cast env from into
        | _ ->
            match Env.find_type ni env with
            | Some { typ = Alias into; _ } -> check_cast env from into
            | _ -> None
        end
  | Named (nm, _), _ ->
      begin match Env.find_type nm env with
      | Some { typ = Alias from; _ } -> check_cast env from into
      | _ -> None
      end
  | _, Named (nm, _) ->
      begin match Env.find_type nm env with
      | Some { typ = Alias into; _ } -> check_cast env from into
      | _ -> None
      end
  (* Casts of Product and List types are not allowed. Similarly, we can't cast
   * Any types (which should actually never appear in an expression type,
   * it would instead be a Named type) *)
  | _, _ -> None

(* Utility for extracting information about a type from the type and env *)
let typ_subst (map : Semant.typ StringMap.t) (t : Semant.typ) : Semant.typ =
  let rec subst (t : Semant.typ) : Semant.typ =
    match t with
    | Any | Unknown | Void | Bool | SInt8 | SInt16 | SInt32 | SInt64
    | UInt8 | UInt16 | UInt32 | UInt64 | Float32 | Float64 | StateRef
    | String | Char -> t
    | Function (ret, args) -> Function (subst ret, List.map subst args)
    | Product ts -> Product (List.map subst ts)
    | List t -> List (subst t)
    | Named (nm, args) -> Named (nm, List.map subst args)
  in subst t

let enum_info_of_type (env : env) (ty : Semant.typ)
  : (string * enum_info) option =
  match ty with
  | Named (nm, tys) ->
      begin match Env.find_type nm env with
      | Some { ty_args; typ = Enum info } ->
          let vars_map = StringMap.of_list (List.combine ty_args tys)
          in let { constrs; typs } = info
          in let typs = Iarray.map (List.map (typ_subst vars_map)) typs
          in Some (nm, { constrs; typs })
      | _ -> None
      end
  | _ -> None

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
    | Char      -> Ok Char
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
              error { ty_args = "_" :: List.map (fun _ -> "_") ty_args;
                      typ = Alias Unknown} ty.pos
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

type sem_expr = Expr of Semant.expr
              | Elem of Semant.elem
              (* An unapplied element *)
              | UElem of Semant.elem * Parsed.name * Semant.typ list

type expr_res = { ast : sem_expr; can_raise : bool }
type as_expr_res = { ast : Semant.expr; can_raise : bool }
type as_elem_res = { ast : Semant.elem; can_raise : bool }

let ok_expr (ast : Semant.expr_base) (typ : Semant.typ) (can_raise : bool)
  : expr_res err = Ok { ast = Expr { ast; typ }; can_raise }

let err_expr ast typ can_raise =
  error ({ ast = Expr { ast; typ }; can_raise } : expr_res)

type kind = Boolean | Numeric | Integer | Primitive | Arbitrary
type type_check = Correct | Incorrect | IsUnknown

let string_of_kind = function
  | Boolean -> "bool"
  | Numeric -> "numeric type"
  | Integer -> "integer type"
  | Primitive -> "primitive type"
  | Arbitrary -> "any type"

let check_types_eq env (k : kind)
  (ty1 : Semant.typ) pos1 (ty2 : Semant.typ) pos2
  ast typ can_raise : expr_res err =
  let check (ty : Semant.typ) : type_check =
    match k, ty with
    | _, Unknown -> IsUnknown
    | Boolean,     Bool
    | Integer,   ( SInt8 | SInt16 | SInt32 | SInt64
                 | UInt8 | UInt16 | UInt32 | UInt64 )
    | Numeric,   ( SInt8 | SInt16 | SInt32 | SInt64
                 | UInt8 | UInt16 | UInt32 | UInt64
                 | Float32 | Float64 )
    | Primitive, ( SInt8 | SInt16 | SInt32 | SInt64
                 | UInt8 | UInt16 | UInt32 | UInt64
                 | Float32 | Float64 | String | Char )
    | Arbitrary, _
        -> Correct
    | _, _ -> Incorrect
  in match check ty1, check ty2 with
  | Correct, Correct ->
      if types_match env ty1 ty2
      then ok_expr ast typ can_raise
      else
        err_expr ast Semant.Unknown can_raise pos2
          "Type error, expected %s but found %s"
          (string_of_type ty1) (string_of_type ty2)
  | Correct, Incorrect ->
      err_expr ast Semant.Unknown can_raise pos2
        "Type error, expected %s but found %s"
        (string_of_type ty1) (string_of_type ty2)
  | Incorrect, Correct ->
      err_expr ast Semant.Unknown can_raise pos1
        "Type error, expected %s but found %s"
        (string_of_type ty2) (string_of_type ty1)
  | Incorrect, Incorrect ->
      prepend_error
        (err_expr ast Semant.Unknown can_raise pos2
          "Type error, expected %s but found %s"
          (string_of_kind k) (string_of_type ty2))
        pos1 "Type error, expected %s but found %s"
        (string_of_kind k) (string_of_type ty1)
  | IsUnknown, Correct | Correct, IsUnknown | IsUnknown, IsUnknown ->
      ok_expr ast Semant.Unknown can_raise
  | IsUnknown, Incorrect ->
      err_expr ast Semant.Unknown can_raise pos2
        "Type error, expected %s but found %s"
        (string_of_kind k) (string_of_type ty2)
  | Incorrect, IsUnknown ->
      err_expr ast Semant.Unknown can_raise pos2
        "Type error, expected %s but found %s"
        (string_of_kind k) (string_of_type ty2)

let rec analyze_expr_or_elem (env : env) (e : Parsed.expr) : expr_res err =
  match e.ast with
  | Id (nm, tys) ->
      begin match Env.find_value nm env with
      | Some (Local { unique; typ }) ->
          if List.is_empty tys
          then ok_expr (Id (unique, [])) typ false
          else err_expr (Id (unique, [])) typ false e.pos
                "Cannot apply types to local variable '%s'" nm
      | Some (Attribute { local; ty }) ->
          let res : Semant.expr_base =
            Attribute ((if local then LocalTop else StateTop), nm)
          in if List.is_empty tys
          then ok_expr res ty false
          else err_expr res ty false e.pos
                "Cannot apply types to attribute '%s'" nm
      | Some (Element { local; tys = arg_tys }) ->
          let res : expr_res =
            { ast = UElem (
                (if local then LocalTop else StateTop),
                { ast = nm; pos = e.pos },
                arg_tys);
              can_raise = false }
          in if List.is_empty tys
          then Ok res
          else error res e.pos "Cannot apply types to element '%s'" nm
      | Some (Uninterp { ty_args; args; ret }) ->
          let^ tys = map_err (analyze_type env) tys
          in let^ vars_map =
            let^ tys =
              if List.length tys = List.length ty_args
              then Ok tys
              else error (match_length ty_args tys Semant.Unknown) e.pos
                    "Function '%s' expected %d arguments but provided %d"
                    nm (List.length ty_args) (List.length tys)
            in Ok (StringMap.of_list (List.combine ty_args tys))
          in let args = List.map (typ_subst vars_map) args
          in let ret = typ_subst vars_map ret
          in ok_expr (Uninterpreted (args, ret, nm)) (Function (ret, args))
              false
      | Some (Function { ty_args; args; ret; body }) ->
          let^ tys = map_err (analyze_type env) tys
          in let^ vars_map =
            let^ tys =
              if List.length tys = List.length ty_args
              then Ok tys
              else error (match_length ty_args tys Semant.Unknown) e.pos
                    "Function '%s' expected %d arguments but provided %d"
                    nm (List.length ty_args) (List.length tys)
            in Ok (StringMap.of_list (List.combine ty_args tys))
          in let args = List.map (fun ((nm : Parsed.name), t) ->
              (nm.ast, typ_subst vars_map t)
            ) args
          in let arg_tys = List.map snd args
          in let ret = typ_subst vars_map ret
          in ok_expr (Interpreted (args, ret, body)) (Function (ret, arg_tys))
              false
      | None ->
          err_expr (Id (nm, [])) Unknown false e.pos
            "Undefined variable '%s'" nm
      end
  | BoolLit b   -> ok_expr (BoolLit b)    Bool    false
  | Int8Lit i   -> ok_expr (Int8Lit i)    SInt8   false
  | Int16Lit i  -> ok_expr (Int16Lit i)   SInt16  false
  | Int32Lit i  -> ok_expr (Int32Lit i)   SInt32  false
  | Int64Lit i  -> ok_expr (Int64Lit i)   SInt64  false
  | UInt8Lit i  -> ok_expr (UInt8Lit i)   UInt8   false
  | UInt16Lit i -> ok_expr (UInt16Lit i)  UInt16  false
  | UInt32Lit i -> ok_expr (UInt32Lit i)  UInt32  false
  | UInt64Lit i -> ok_expr (UInt64Lit i)  UInt64  false
  | F32Lit f    -> ok_expr (F32Lit f)     Float32 false
  | F64Lit f    -> ok_expr (F64Lit f)     Float64 false
  | StringLit s -> ok_expr (StringLit s)  String  false
  | CharLit c   -> ok_expr (CharLit c)    Char    false
  | UnitLit     -> ok_expr UnitLit        Void    false
  | UnaryExp (op, ex) ->
      let^ { ast = exp; can_raise } = analyze_expr env ex
      in begin match op, exp.typ with
      | BNot, (Bool | Unknown) ->
          ok_expr (UnaryExp (BNot, exp)) exp.typ can_raise
      | BNot, _ ->
          err_expr (UnaryExp (BNot, exp)) Unknown can_raise ex.pos
            "Expected a bool, found %s" (string_of_type exp.typ)
      | (Neg | LNot),
        (SInt8 | SInt16 | SInt32 | SInt64 | UInt8 | UInt16 | UInt32 | UInt64
          | Unknown)
        -> ok_expr (UnaryExp (op, exp)) exp.typ can_raise
      | (Neg | LNot), _ ->
          err_expr (UnaryExp (op, exp)) Unknown can_raise ex.pos
            "Expected an integer, found %s" (string_of_type exp.typ)
      end
  | BinaryExp (l, op, r) ->
      let^ { ast = lhs; can_raise = lhs_raise } = analyze_expr env l
      in let^ { ast = rhs; can_raise = rhs_raise } = analyze_expr env r
      in let can_raise = lhs_raise || rhs_raise
      in begin match op with
      (* Boolean operations *)
      | LAnd | LOr ->
          check_types_eq env Boolean lhs.typ l.pos rhs.typ r.pos
            (BinaryExp (lhs, op, rhs)) Bool can_raise
      (* Numeric operations *)
      | Mul | Div | Add | Sub ->
          check_types_eq env Numeric lhs.typ l.pos rhs.typ r.pos
            (BinaryExp (lhs, op, rhs)) lhs.typ can_raise
      (* Integer operations *)
      | Mod | LShft | RShft | BAnd | BXor | BOr ->
          check_types_eq env Integer lhs.typ l.pos rhs.typ r.pos
            (BinaryExp (lhs, op, rhs)) lhs.typ can_raise
      (* Comparison operations (apply to numeric types, string, and char) *)
      | Lt | Le | Gt | Ge ->
          check_types_eq env Primitive lhs.typ l.pos rhs.typ r.pos
            (BinaryExp (lhs, op, rhs)) Bool can_raise
      (* Equality operations (apply to any types) *)
      | Eq | Ne ->
          check_types_eq env Arbitrary lhs.typ l.pos rhs.typ r.pos
            (BinaryExp (lhs, op, rhs)) Bool can_raise
      end
  (* TODO: FieldExp *)
  | ProdField (ex, { ast = idx; _ }) ->
      let^ { ast = exp; can_raise } = analyze_expr env ex
      in begin match exp.typ with
      | Product ts ->
          begin match List.nth_opt ts idx with
          | None ->
              err_expr (ProdField (exp, idx)) Semant.Unknown can_raise e.pos
                "No index %d in type %s" idx (string_of_type exp.typ)
          | Some t ->
              ok_expr (ProdField (exp, idx)) t can_raise
          end
      | Unknown -> ok_expr (ProdField (exp, idx)) Semant.Unknown can_raise
      | _ ->
          err_expr (ProdField (exp, idx)) Semant.Unknown can_raise ex.pos
            "Expected a product type but found %s" (string_of_type exp.typ)
      end
  | CastExp (ex, ty) ->
      let^ { ast = exp; can_raise } = analyze_expr env ex
      in let^ typ = analyze_type env ty
      in begin match check_cast env exp.typ typ with
      | Some res_ty -> ok_expr (CastExp (exp, typ)) res_ty can_raise
      | None ->
          err_expr (CastExp (exp, typ)) Semant.Unknown can_raise e.pos
            "Invalid cast, cannot cast %s to %s"
            (string_of_type exp.typ) (string_of_type typ)
      end
  | TupleExp es ->
      let^ (es, can_raise, ts) = List.fold_right (fun e acc ->
          let^ (es, can_raise, ts) = acc
          in let^ { ast = exp; can_raise = e_raise } = analyze_expr env e
          in Ok (exp :: es, can_raise || e_raise, exp.typ :: ts)
        ) es (Ok ([], false, []))
      in ok_expr (TupleExp es) (Product ts) can_raise
  | StructExp (strct, tys, fields) ->
      let^ tys = map_err (analyze_type env) tys
      in let^ field_tys =
        match Env.find_type strct.ast env with
        | Some { ty_args; typ = Struct fields } ->
            let^ vars_map =
              let^ tys =
                if List.length tys = List.length ty_args
                then Ok tys
                else error (match_length ty_args tys Semant.Unknown) strct.pos
                      "Type '%s' expected %d arguments but provided %d"
                      strct.ast (List.length ty_args) (List.length tys)
              in Ok (StringMap.of_list (List.combine ty_args tys))
            in let fields = StringMap.map (typ_subst vars_map) fields
            in Ok fields
        | Some _ ->
            error (StringMap.of_list
                      (List.map (fun ((f : Parsed.name), _) ->
                        (f.ast, Semant.Unknown)) fields))
              strct.pos "Type '%s' is not a struct" strct.ast
        | None ->
            error (StringMap.of_list
                      (List.map (fun ((f : Parsed.name), _) ->
                        (f.ast, Semant.Unknown)) fields))
              strct.pos "Undefined type '%s'" strct.ast
      in let^ (fields, can_raise, unset) =
        List.fold_right (fun ((f : Parsed.name), ex) acc ->
          let^ (fields, can_raise, unset) = acc
          in let^ { ast = exp; can_raise = ex_raise } = analyze_expr env ex
          in if not (StringSet.mem f.ast unset)
          then
            error ((f.ast, exp) :: fields, can_raise || ex_raise, unset)
              f.pos "Duplicate field '%s'" f.ast
          else
            let res = (
              (f.ast, exp) :: fields,
              can_raise || ex_raise,
              StringSet.remove f.ast unset) 
            in match StringMap.find_opt f.ast field_tys with
            | Some t ->
                if types_match env exp.typ t
                then Ok res
                else error res ex.pos "Type mismatch, expected %s but found %s"
                      (string_of_type t) (string_of_type exp.typ)
            | None ->
                error res f.pos "No such field '%s' for struct '%s'"
                  f.ast strct.ast
        ) fields (Ok ([], false, StringSet.empty))
      in let res_exp = Semant.StructExp (strct.ast, tys, fields)
      in let res_typ = Semant.Named (strct.ast, tys)
      in if StringSet.is_empty unset
      then ok_expr res_exp res_typ can_raise
      else
        err_expr res_exp res_typ can_raise e.pos
          "Missing fields %s" (String.concat ", " (StringSet.to_list unset))
  | EnumExp (enum, tys, constr, args) ->
      let^ tys = map_err (analyze_type env) tys
      in let^ arg_tys =
        match Env.find_type enum.ast env with
        | Some { ty_args; typ = Enum { constrs; typs } } ->
            let^ vars_map =
              let^ tys =
                if List.length tys = List.length ty_args
                then Ok tys
                else error (match_length ty_args tys Semant.Unknown) enum.pos
                      "Type '%s' expected %d arguments but provided %d"
                      enum.ast (List.length ty_args) (List.length tys)
              in Ok (StringMap.of_list (List.combine ty_args tys))
            in begin match StringMap.find_opt constr.ast constrs with
            | Some i ->
                let arg_tys = List.map (typ_subst vars_map) (Iarray.get typs i)
                in if List.length args = List.length arg_tys
                then Ok arg_tys
                else
                  error (match_length args arg_tys Semant.Unknown) constr.pos
                    "Constructor '%s' expected %d arguments but provded %d"
                    constr.ast (List.length arg_tys) (List.length args)
            | None ->
                error (List.map (fun _ -> Semant.Unknown) args) constr.pos
                  "No such constructor '%s' for enum '%s'"
                  constr.ast enum.ast
            end
        | Some _ ->
            error (List.map (fun _ -> Semant.Unknown) args) enum.pos
              "Type '%s' is not an enum" enum.ast
        | None ->
            error (List.map (fun _ -> Semant.Unknown) args) enum.pos
              "Undefined type '%s'" enum.ast
      in let^ (args, can_raise) =
        List.fold_right2 (fun ex ty acc ->
          let^ (args, can_raise) = acc
          in let^ { ast = exp; can_raise = ex_raise } = analyze_expr env ex
          in let res = (exp :: args, can_raise || ex_raise)
          in if types_match env exp.typ ty
          then Ok res
          else
            error res ex.pos "Type mismatched, expected %s but found %s"
              (string_of_type ty) (string_of_type exp.typ)
        ) args arg_tys (Ok ([], false))
      in ok_expr (EnumExp (enum.ast, tys, constr.ast, args))
            (Semant.Named (enum.ast, tys)) can_raise
  (* TODO: FuncExp *)
  | CondExp (c, t, el) ->
      let^ { ast = cond; can_raise = cond_raise } = analyze_cond env c
      in let^ { ast = thn; can_raise = thn_raise } = analyze_expr env t
      in let^ { ast = els; can_raise = els_raise } = analyze_expr env el
      in let can_raise = cond_raise || thn_raise || els_raise
      in if types_match env thn.typ els.typ
      then ok_expr (CondExp (cond, thn, els)) thn.typ can_raise
      else
        err_expr (CondExp (cond, thn, els)) Semant.Unknown can_raise e.pos
          "Type mismatch in branches, found %s and %s"
          (string_of_type thn.typ) (string_of_type els.typ)
  | Exists e ->
      let^ { ast = elem; can_raise } = analyze_elem env e
      in ok_expr (Exists elem) Bool can_raise
  (* TODO: ForEach, ForAll *)
  (* Constructors not used by the parser *)
  | Element _ | Attribute _ | Interpreted _ | Uninterpreted _ -> .

and analyze_expr (env : env) (e : Parsed.expr) : as_expr_res err =
  let^ { ast; can_raise } = analyze_expr_or_elem env e
  in match ast with
  | Expr res -> Ok ({ ast = res; can_raise } : as_expr_res)
  | Elem elem -> 
      Ok { ast = { ast = Semant.Element elem; typ = StateRef }; can_raise }
  | UElem (base, elem, _) ->
      error ({ ast =
        { ast = Semant.Element (Nested (base, elem.ast, [])); typ = Unknown };
        can_raise 
      } : as_expr_res) elem.pos "Missing argument application"

and analyze_elem (env : env) (e : Parsed.expr) : as_elem_res err =
  let^ { ast = res; can_raise } = analyze_expr_or_elem env e
  in match res with
  | Elem elem -> Ok { ast = elem; can_raise }
  | UElem (base, elem, _) ->
      error { ast = Nested (base, elem.ast, []); can_raise } elem.pos
        "Missing argument application"
  | Expr _ ->
      error {ast = Semant.StateTop; can_raise } e.pos "Not an element"

(* Utilities for analyzing expressions of certain types *)
and analyze_cond (env : env) (e : Parsed.expr) : as_expr_res err =
  let^ { ast; can_raise } = analyze_expr env e
  in let res : as_expr_res = { ast; can_raise }
  in match ast.typ with
  | Bool | Unknown -> Ok res
  | _ -> error res e.pos "Expected a bool, found %s" (string_of_type ast.typ)

and analyze_expr_for_type (env : env) (t : Semant.typ) (e : Parsed.expr)
  : as_expr_res err =
  let^ { ast; can_raise } = analyze_expr env e
  in let res : as_expr_res = { ast; can_raise }
  in if types_match env ast.typ t
  then Ok res
  else
    error res e.pos "Incorrect type, expected %s but found %s"
      (string_of_type t) (string_of_type ast.typ)

(* Semantic analysis of statements, provided the current environment and a
 * context that tells us the return type of the current function and whether we
 * are allowed to yield or not and if so the type *)
type stmt_context = { ret : Semant.typ; yield : Semant.typ ref option }

(* Continue field indicates whether the statement after is reachable.
 * For each statement we record whether it CAN continue to the next statement,
 * return, raise an exception, or yield. *)
type stmt_cont = { contu : bool; ret : bool; raise : bool; yield : bool }
type stmt_res  = { env : env; res : Semant.stmt; cont : stmt_cont }

let reachable (x : stmt_cont) : bool = let { contu; _ } = x in contu
let continue : stmt_cont =
  { contu = true; ret = false; raise = false; yield = false }
let may_raise (raise : bool) =
  { contu = true; ret = false; raise; yield = false }

(* Loops can always continue to the next statement (since they may not be
 * entered), never yield (since they absorb the yield), but can return or raise
 * if the body does *)
let loop_cont (lst_raise : bool) (b : stmt_cont) =
  { contu = true; ret = b.ret; raise = b.raise || lst_raise; yield = false }

let cont_branches (cond_raise : bool) (x : stmt_cont) (y : stmt_cont) =
  { contu = x.contu || y.contu;  ret   = x.ret   || y.ret;
    yield = x.yield || y.yield;  raise = x.raise || y.raise || cond_raise }

let cont_try_catch (b : stmt_cont) (c : stmt_cont) (f : stmt_cont)
  : stmt_cont =
  {
    (* We can continue if the body and finally can continue, or if the body can
     * raise and the catch and finally can continue *)
    contu = (b.contu && f.contu) || (b.raise && c.contu && f.contu);
    (* We can return if the body can return, if finally can return, or if the
     * body can raise and the catch can return *)
    ret = b.ret || f.ret || (b.raise && c.ret);
    (* We can raise if the body or finally can raise. *)
    raise = b.raise || f.raise;
    (* We can yield if the body or finally can yield or if the body can raise
     * and catch can yield *)
    yield = b.yield || f.yield || (b.raise && c.yield)
  }

let rec analyze_stmt (env : env) (ctx : stmt_context) (s : Parsed.stmt)
  : stmt_res err =
  match s.ast with
  | ForLoop (v, ex, body) ->
      let^ { ast = exp; can_raise } = analyze_expr env ex
      in let^ elem_ty =
        match exp.typ with
        | List t -> Ok t
        | Unknown -> Ok Semant.Unknown (* an error will already have occured *)
        | t -> error Semant.Unknown ex.pos "Expected a list, found %s"
                (string_of_type t)
      in let (unique, body_env) = add_local v elem_ty env
      (* We choose not to allow yields from statement loops *)
      in let body_ctx = { ret = ctx.ret; yield = None }
      in let^ (body, cont) = analyze_stmts body_env body_ctx body
      in Ok { env; res = Semant.ForLoop (unique, exp, body);
              cont = loop_cont can_raise cont }
  | ForElem (base, elem, vs, body) ->
      let^ { ast = base; can_raise } =
        match base with
        | None -> Ok { ast = Semant.StateTop; can_raise = false }
        | Some base -> analyze_elem env base
      in let^ var_tys =
        match Env.find_value elem.ast env with
        | Some (Element { tys; _ }) ->
            if List.length tys = List.length vs
            then Ok tys
            else error (match_length vs tys Semant.Unknown) elem.pos
                  "Element '%s' has %d arguments but %d variables provided"
                  elem.ast (List.length tys) (List.length vs)
        | None -> error (List.map (fun _ -> Semant.Unknown) vs) elem.pos
                    "Undefined element '%s'" elem.ast
        | Some _ -> error (List.map (fun _ -> Semant.Unknown) vs) elem.pos
                      "Value '%s' is not an element" elem.ast
      in let^ (uniques, body_env) = add_locals s.pos vs var_tys env
      in let body_ctx = { ret = ctx.ret; yield = None }
      in let^ (body, cont) = analyze_stmts body_env body_ctx body
      in Ok { env; res = Semant.ForElem (Some base, elem.ast, uniques, body);
              cont = loop_cont can_raise cont }
  | WhileLoop (cond, body) ->
      let^ { ast = cond; can_raise } = analyze_cond env cond
      (* We choose not to allow yields from while loops *)
      in let body_ctx = { ret = ctx.ret; yield = None }
      in let^ (body, cont) = analyze_stmts env body_ctx body
      in Ok { env; res = Semant.WhileLoop (cond, body);
              cont = loop_cont can_raise cont }
  | IfThenElse (cond, thn, els) ->
      let^ { ast = cond; can_raise } = analyze_cond env cond
      in let^ (thn, thn_cont) = analyze_stmts env ctx thn
      in let^ (els, els_cont) = analyze_stmts env ctx els
      in Ok { env; res = Semant.IfThenElse (cond, thn, els);
              cont = cont_branches can_raise thn_cont els_cont }
  | Match (e, (cases, default)) ->
      let^ { ast = expr; can_raise } = analyze_expr env e
      in let^ ty_info =
        match enum_info_of_type env expr.typ with
        | Some info -> Ok (Some info)
        | None -> error None e.pos "Not an enum type, found %s"
                    (string_of_type expr.typ)
      in let case_info pos (enum : Parsed.name) (constr : Parsed.name)
        (vs : Parsed.name list) : (int * Semant.typ list) err =
        match ty_info with
        (* If the scrutinee isn't an enum, we just return unknown types *)
        | None -> Ok (-1, List.map (fun _ -> Semant.Unknown) vs)
        | Some (nm, info) ->
            let res =
              match StringMap.find_opt constr.ast info.constrs with
              | None ->
                  error (-1, List.map (fun _ -> Semant.Unknown) vs) constr.pos
                    "Undefined constructor '%s'" constr.ast
              | Some i ->
                  let tys = Iarray.get info.typs i
                  in if List.length tys = List.length vs
                  then Ok (i, tys)
                  else
                    error (i, match_length vs tys Semant.Unknown) pos
                      "Constructor '%s' has %d arguments but %d variables provided"
                      constr.ast (List.length tys) (List.length vs)
            in if nm = enum.ast
            then res
            else
              prepend_error res enum.pos
                "Expected case for type '%s' but found '%s'" nm enum.ast
      in let^ (cases_map, cases_cont) =
        List.fold_left (fun acc ((pat : Parsed.pattern), body) ->
          let^ (cases_map, cont) = acc
          in let vs = pat.ast.vars
          in let^ (idx, tys) = case_info pat.pos pat.ast.enum pat.ast.constr vs
          in let^ (uniques, body_env) = add_locals pat.pos vs tys env
          in let^ (body, case_cont) = analyze_stmts body_env ctx body
          in let res =
            (IntMap.add idx (uniques, body) cases_map,
             cont_branches false cont case_cont)
          in if not (IntMap.mem idx cases_map)
          then Ok res
          else error res pat.pos "Duplicate case for %s::%s"
                pat.ast.enum.ast pat.ast.constr.ast
        ) (Ok (IntMap.empty, 
              { contu = false; ret = false; raise = false; yield = false }))
        cases
      in let^ (default_body, default_cont) = analyze_stmts env ctx default
      (* Note that we can use cont_branches can_raise cases_cont default_cont
       * as a reasonable approximation of the continuation, including
       * default_cont is not necessary if the default is never used but that
       * is also an error, so it's possible this could suppress an error but
       * that'll occur sometimes when other errors occur like this so it's
       * fine *)
      in begin match ty_info with
      (* If we don't have the type information we need, just generate a
       * placeholder, an error will have been generated by now *)
      | None -> Ok { env; res = Semant.Match (expr, Iarray.of_list []);
                     cont = cont_branches can_raise cases_cont default_cont }
      | Some (_, { constrs; _ }) ->
          let cases_res =
            Iarray.init (StringMap.cardinal constrs) (fun i ->
              Option.value ~default:([], default_body)
                (IntMap.find_opt i cases_map))
          in let res =
            { env; res = Semant.Match (expr, cases_res);
              cont = cont_branches can_raise cases_cont default_cont }
          in if (IntMap.cardinal cases_map < StringMap.cardinal constrs)
              || List.is_empty default
          then Ok res
          else error res s.pos "Unused default case"
      end
  | TryCatch (body, catch, finally) ->
      let^ (body, body_cont) = analyze_stmts env ctx body
      in let^ (catch, catch_cont) =
        match catch with
        | None -> Ok (None, continue)
        | Some (excpt, vs, b) ->
            let^ tys =
              match Env.find_except excpt.ast env with
              | Some tys ->
                  if List.length tys = List.length vs
                  then Ok tys
                  else error (match_length vs tys Semant.Unknown) excpt.pos
                        "Exception '%s' has %d arguments but %d provided"
                        excpt.ast (List.length tys) (List.length vs)
              | None -> error (List.map (fun _ -> Semant.Unknown) vs) excpt.pos
                          "Undefined exception '%s'" excpt.ast
            in let^ (uniques, catch_env) = add_locals s.pos vs tys env
            in let^ (b, b_cont) = analyze_stmts catch_env ctx b
            in Ok (Some (excpt.ast, uniques, b), b_cont)
      in let^ (finally, finally_cont) = analyze_stmts env ctx finally
      in Ok { env; res = Semant.TryCatch (body, catch, finally);
              cont = cont_try_catch body_cont catch_cont finally_cont }
  | Clear elem ->
      let^ { ast = elem; can_raise } = analyze_elem env elem
      in Ok { env; res = Semant.Clear elem; cont = may_raise can_raise }
  | Touch elem ->
      let^ { ast = elem; can_raise } = analyze_elem env elem
      in Ok { env; res = Semant.Touch elem; cont = may_raise can_raise }
  | Assert e ->
      let^ { ast = e; _ } = analyze_cond env e
      in begin match e.ast with
      | Semant.BoolLit false ->
          Ok { env; res = Semant.Assert e;
               cont =
                 { contu = false; ret = false; raise = true; yield = false } }
      | _ -> Ok { env; res = Semant.Assert e; cont = may_raise true }
      end
  | Return e ->
      let^ { ast = exp; can_raise } = analyze_expr env e
      in let res =
        { env; res = Semant.Return exp;
          cont =
            { contu = false; ret = true; raise = can_raise; yield = false } }
      in if types_match env exp.typ ctx.ret
      then Ok res
      else error res s.pos "Incorrect return type, expected %s but found %s"
            (string_of_type ctx.ret) (string_of_type exp.typ)
  | Yield e ->
      let^ { ast = exp; can_raise } = analyze_expr env e
      in let res =
        { env; res = Semant.Yield exp;
          cont =
            { contu = false; ret = false; raise = can_raise; yield = true } }
      in begin match ctx.yield with
      | None -> error res s.pos "Invalid yield, not contained in a for-loop"
      | Some ({ contents = Any } as yield_ty) ->
          yield_ty := exp.typ ; Ok res
      | Some ({ contents = Unknown }) -> Ok res
      | Some ({ contents = yield_ty }) ->
          if types_match env exp.typ yield_ty
          then Ok res
          else error res s.pos "Incorrect yield type, expected %s but found %s"
                (string_of_type yield_ty) (string_of_type exp.typ)
      end
  | Raise (excpt, args) ->
      let^ tys =
        match Env.find_except excpt.ast env with
        | Some tys ->
            if List.length tys = List.length args
            then Ok tys
            else error (match_length args tys Semant.Unknown) excpt.pos
                  "Exception '%s' has %d arguments but %d provided"
                  excpt.ast (List.length tys) (List.length args)
        | None -> error (List.map (fun _ -> Semant.Unknown) args) excpt.pos
                    "Undefined exception '%s'" excpt.ast
      in let^ args =
        map2_err (fun ty ex ->
          let^ { ast; _ } = analyze_expr_for_type env ty ex in Ok ast
        ) tys args
      in Ok { env; res = Semant.Raise (excpt.ast, args);
              cont =
                { contu = false; ret = false; raise = true; yield = false } }
  | Assign (lhs, rhs) ->
      let^ { ast = lhs; can_raise = lhs_raise } = analyze_expr env lhs
      in let^ { ast = rhs; can_raise = rhs_raise } = analyze_expr env rhs
      in let res =
        { env; res = Semant.Assign (lhs, rhs);
          cont =
            { contu = true; ret = false; raise = lhs_raise || rhs_raise;
              yield = false } }
      in if types_match env lhs.typ rhs.typ
      then Ok res
      else error res s.pos "Mismatched types, %s and %s"
            (string_of_type lhs.typ) (string_of_type rhs.typ)
  | LetStmt (v, ty, exp) ->
      let^ { ast = exp; can_raise = raise } = analyze_expr env exp
      in let^ t =
        match ty with
        | None -> Ok exp.typ
        | Some ty ->
            let^ ty = analyze_type env ty
            in if types_match env exp.typ ty
            then Ok ty
            else error ty s.pos "Type mismatched, expected %s but found %s"
                  (string_of_type ty) (string_of_type exp.typ)
      in let (unique, env) = add_local v t env
      in Ok { env; res = Semant.LetStmt (unique, None, exp);
              cont = { contu = true; ret = false; raise; yield = false } }
  | Localize body ->
      let^ (body, cont) = analyze_stmts env ctx body
      in Ok { env; res = Semant.Localize body; cont }

and analyze_stmts (env : env) (ctx : stmt_context) (stmts : Parsed.stmt list)
  : (Semant.stmt list * stmt_cont) err =
  match stmts with
  | [] -> Ok ([], { contu = true; ret = false; raise = false; yield = false })
  | s :: tl ->
      let^ { env; res = s_res; cont = s_cont } = analyze_stmt env ctx s
      in let^ (tl_res, tl_cont) = analyze_stmts env ctx tl
      in let res = (s_res :: tl_res, tl_cont)
      in if s_cont.contu
      then Ok res
      else
        match tl with
        | [] -> Ok res
        | un :: _ -> error res un.pos "Unreachable statement"

let analyze_function (env : env) pos (ret : Semant.typ)
  (stmts : Parsed.stmt list) : Semant.stmt list err =
  let^ (res, cont) = analyze_stmts env { ret; yield = None } stmts
  in if not cont.contu
  then Ok res
  else
    match ret with
    | Void -> Ok (res @ [Semant.Return { ast = UnitLit; typ = Void }])
    | _ -> error res pos "Control can reach end of function without return"

(* Analyze type declarations
 * - Step 1: Collect all the type names to ensure there are no repeated names
 * - Step 2: Process each type to provide a real definition and ensure all
 *    named types exist and are properly used
 * The input, tys, contains only decl of the form Enum _, Struct _, or Type _
 *)
(* TODO: Identify and error on cyclic type definitions. Replace such types with
 * Unknown because otherwise other analyses (such as type equivalence) may
 * break *)
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
            ~err:(fun () -> error env d.pos "Type %s already defined" name.ast)
            (Env.add_type name.ast {
              ty_args = List.map (fun (t : Parsed.name) -> t.ast) ty_args;
              typ = Alias Unknown } env)
      | Type { name; _ } ->
          of_option
            ~err:(fun () -> error env d.pos "Type %s already defined" name.ast)
            (Env.add_type name.ast { ty_args = []; typ = Alias Unknown } env)
      | _ -> failwith "Match error"
    ) (Ok env) tys
  (* Step 2 *)
  in let^ () =
    List.fold_left (fun acc (d : Parsed.decl) ->
      let^ () = acc
      in match d.ast with
      | Enum { name; ty_args; constrs } ->
          let info =
            match Env.find_type name.ast env with
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
              | ((c : Parsed.name), _) :: tl ->
                  Seq.Cons ((c.ast, i), gen tl (i+1))
            in gen constrs 0)
          in Ok (info.typ <- Enum { constrs; typs })
      | Struct { name; ty_args; fields } ->
          let info =
            match Env.find_type name.ast env with
            | None -> failwith "Map error"
            | Some info -> info
          in let typ_env = add_ty_args env ty_args
          in let^ fields =
            map_err 
              (fun ((f : Parsed.name), t) -> 
                err_map (fun t -> (f.ast, t)) (analyze_type typ_env t))
              fields
          in Ok (info.typ <- Struct (StringMap.of_list fields))
      | Type { name; def } ->
          let info =
            match Env.find_type name.ast env with
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
            ~err:(fun() ->
              error env d.pos "Exception %s already defined" name.ast)
            (Env.add_except name.ast tys env)
    | Uninterp { name; ty_args; args; ret } ->
        let typ_env = add_ty_args env ty_args
        in let^ args = map_err (analyze_type typ_env) args
        in let^ ret = analyze_type typ_env ret
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name.ast)
            (Env.add_unique name.ast
              (Uninterp {
                ty_args = List.map (fun (t : Parsed.name) -> t.ast) ty_args;
                args; ret }) env)
    | Attribute { local; name; ty } ->
        let^ ty = analyze_type env ty
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name.ast)
            (Env.add_unique name.ast (Attribute { local; ty }) env)
    | Element { local; name; ty } ->
        let^ tys = map_err (analyze_type env) ty
        in of_option
            ~err:(fun () -> error env d.pos "Name %s already defined" name.ast)
            (Env.add_unique name.ast (Element { local; tys }) env)
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
            let rec find_dups (nms : (Parsed.name * 'a) list) : unit err =
              match nms with
              | [] -> Ok ()
              | (nm, _) :: tl ->
                  let^ () =
                    if List.exists
                        (fun ((x : Parsed.name), _) -> x.ast = nm.ast) tl
                    then
                      error () nm.pos "Multiple arguments named %s" nm.ast
                    else Ok ()
                  in find_dups tl
            in find_dups args
          in let^ args = map_err (fun (nm, t) ->
            err_map (fun t -> (nm, t)) (analyze_type typ_env t)
          ) args
          in let^ ret = analyze_type typ_env ret
          in of_option
              ~err:(fun () ->
                error env d.pos "Name %s already defined" name.ast)
              (Env.add_unique name.ast
                (Function {
                  ty_args = List.map (fun (t : Parsed.name) -> t.ast) ty_args;
                  args; ret; body = ref [] }) env)
      | _ -> failwith "Match error"
    ) (Ok env) funcs
  (* Step 2 *)
  in let^ () =
    List.fold_left (fun acc (d : Parsed.decl) ->
      let^ () = acc
      in match d.ast with
      | Function { name; ty_args; body; _ } ->
          let info =
            match Env.find_value name.ast env with
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
          in let^ body = analyze_function body_env d.pos info.ret body
          in Ok (info.body := body)
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
