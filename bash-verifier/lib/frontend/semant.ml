(* Semantic analysis, in this stage we:
 * - Type check the program and assign types to every expression
 * - Check the placement of return and yield statements and ensure all non-void
 *   functions have return statements
 * - Assign unique names to each variable used in a procedure to eliminate
 *   shadowing
 *)
open Ast
open Utils

module StringMap = Map.Make(String)

(* The result of semantic analysis (though we do not use decls in favor of
 * maps) *)
module Semant = struct
  (* For unions we record a map from the constructor name to an index and an
   * array of argument types for each constructor. This is because in code-gen
   * we need to know the position of each constructor *)
  type enum_info = {
    constrs: int StringMap.t;
    typs: typ_annt list Iarray.t
  }

  and typ_base =
    | Void | Bool
    | SInt8 | UInt8 | SInt16 | UInt16 | SInt32 | UInt32 | SInt64 | UInt64
    | Float32 | Float64
    | Function of typ_annt * typ_annt list (* return type and argument types *)
    | StateRef | String
    | Product of typ_annt list | List of typ_annt
    | Struct of typ_annt StringMap.t | Enum of enum_info
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

module Env : sig
  type ('v, 't, 'e) t

  val empty : ('v, 't, 'e) t

  val add_type : string -> 't -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_except : string -> 'e -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_unique : string -> 'v -> ('v, 't, 'e) t -> ('v, 't, 'e) t option
  val add_value : string -> (string -> 'v) -> ('v, 't, 'e) t -> ('v, 't, 'e) t

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
    else Some { types; excepts; values = StringMap.add s (0, x) values }

  let add_value s f { values; types; excepts } =
    { types; excepts;
      values =
        StringMap.update s (function
          | None -> Some (0, f s)
          | Some (i, n) -> Some (i + 1, f (s ^ "." ^ string_of_int i))
        ) values }

  let find_type s { types; _ } = StringMap.find_opt s types

  let find_except s { excepts; _ } = StringMap.find_opt s excepts

  let find_value s { values; _ } = Option.map snd (StringMap.find_opt s values)
  
  let scope m k = k m
end

type value_binding =
  | Uninterp  of { ty_args : string list; args : Semant.typ list;
                    ret : Semant.typ }
  | Attribute of { local : bool; ty : Semant.typ }
  | Element   of { local : bool; tys : Semant.typ list }
  | Function  of { ty_args : string list; args : (string * Semant.typ list);
                    ret : Semant.typ; mutable body : Semant.stmt list ref }
  | Local     of { unique : string; typ : Semant.typ }
type type_binding = { ty_args : string list; mutable typ : Semant.typ }
type except_binding = Semant.typ list

type env = (value_binding, type_binding, except_binding) Env.t

let add_ty_args (env : env) (ty_args : string list) : env =
  List.fold_left (fun env nm ->
    Option.value ~default:env
      (Env.add_type nm { ty_args = []; typ = Semant.Void } env))
    env ty_args

type err_msg = { pos : Lexing.position * Lexing.position; msg : string }
type 'a err = ('a, err_msg) result

let error pos = Printf.ksprintf (fun msg -> { pos; msg })

let ( let^ ) = Result.bind

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
        in let^ args = map_result analyze args
        in Ok (Function (ret, args) : Semant.typ)
    | StateRef  -> Ok StateRef
    | String    -> Ok String
    | Product ts ->
        let^ ts = map_result analyze ts
        in Ok (Semant.Product ts)
    | List t ->
        let^ t = analyze t
        in Ok (Semant.List t)
    | Named (nm, ty_args) ->
        let^ ty_args = map_result analyze ty_args
        in let^ ty_info =
          match Env.find_type nm env with
          | None -> Error (error ty.pos "Undefined type '%s'" nm)
          | Some info -> Ok info
        in if List.length ty_args <> List.length ty_info.ty_args
        then
          Error (error ty.pos "Type '%s' expected %d arguments but provided %d"
            nm (List.length ty_info.ty_args) (List.length ty_args))
        else Ok (Semant.Named (nm, ty_args))
  in analyze ty

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
          Option.to_result
            ~none:(error d.pos "Type %s already defined" name)
            (Env.add_type name { ty_args; typ = Void } env)
      | Type { name; _ } ->
          Option.to_result
            ~none:(error d.pos "Type %s already defined" name)
            (Env.add_type name { ty_args = []; typ = Void } env)
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
            map_result
              (fun (f, ts) ->
                Result.map (fun ts -> (f, ts))
                  (map_result (analyze_type typ_env) ts))
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
            map_result 
              (fun (f, t) -> 
                Result.map (fun t -> (f, t)) (analyze_type typ_env t))
              fields
          in Ok (info.typ <- Struct (StringMap.of_list fields))
      | Type { name; def } ->
          let info =
            match Env.find_type name env with
            | None -> failwith "Map error"
            | Some info -> info
          in let^ def = analyze_type env def
          in Ok (info.typ <- def)
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
        let^ tys = map_result (analyze_type env) ty
        in Option.to_result
            ~none:(error d.pos "Exception %s already defined" name)
            (Env.add_except name tys env)
    | Uninterp { name; ty_args; args; ret } ->
        let typ_env = add_ty_args env ty_args
        in let^ args = map_result (analyze_type typ_env) args
        in let^ ret = analyze_type typ_env ret
        in Option.to_result
            ~none:(error d.pos "Name %s already defined" name)
            (Env.add_unique name (Uninterp { ty_args; args; ret }) env)
    | Attribute { local; name; ty } ->
        let^ ty = analyze_type env ty
        in Option.to_result
            ~none:(error d.pos "Name %s already defined" name)
            (Env.add_unique name (Attribute { local; ty }) env)
    | Element { local; name; ty } ->
        let^ tys = map_result (analyze_type env) ty
        in Option.to_result
            ~none:(error d.pos "Name %s already defined" name)
            (Env.add_unique name (Element { local; tys }) env)
    | _ -> failwith "Match error"
  ) (Ok env) vals

(* Entry point *)
let analyze_program (prg : Parsed.decl list) : env err =
  let env : env = Env.empty
  in let { types; values; funcs } = split_decls prg
  in let^ env = analyze_types env types
  in let^ env = analyze_values env values
  in analyze_funcs env funcs
