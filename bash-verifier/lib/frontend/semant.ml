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
  (* For unions we record a map from the constructor name to an index and an
   * array of argument types for each constructor. This is because in code-gen
   * we need to know the position of each constructor *)
  type union_info = {
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
    | Struct of typ_annt StringMap.t | Enum of typ_annt StringMap.t
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
                    ret : Semant.typ; body : Semant.stmt list ref }
  | Local     of { unique : string; typ : Semant.typ }
type type_binding = { ty_args : string list; typ : Semant.typ }
type except_binding = Semant.typ list

type env = (value_binding, type_binding, except_binding) Env.t

type err_msg = { pos : Lexing.position * Lexing.position; msg : string }
type 'a err = ('a, err_msg) result

let error pos = Printf.ksprintf (fun msg -> { pos; msg })

let ( let^ ) = Result.bind

(* Semantic analysis functions *)
(* Utilities for splitting decls by kind (type, exception, and values) *)
type decls_split = { 
  types : Parsed.decl list;
  excepts : Parsed.decl list;
  values : Parsed.decl list }

let split_decls (ds : Parsed.decl list) : decls_split =
  let (types, excepts, values) =
    List.fold_right (fun (d : Parsed.decl) (types, excepts, values) ->
      match d.ast with
      | Enum _ | Struct _ | Type _ -> (d :: types, excepts, values)
      | Exception _ -> (types, d :: excepts, values)
      | Uninterp _ | Attribute _ | Element _ | Function _ ->
          (types, excepts, d :: values)
    ) ds ([], [], [])
  in { types; excepts; values }

(* Analyze types
 * - Step 1: Collect all the type names to ensure there are no repeated names
 * - Step 2: Process each type to provide a real definition and ensure all
 *    named types exist and are properly used
 * The input, tys, contains only decl of the form Enum _, Struct _, or Type _
 *)
let analyze_types (env : env) (tys : Parsed.decl list) : env err =
  (* Step 1 *)
  let^ with_names =
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
  in let^ processed =
    List.fold_left (fun env (d : Parsed.decl) ->
      let^ env = env
      in match d.ast with
      | Enum { name; ty_args; constrs } ->
          failwith "TODO"
      | Struct { name; ty_args; fields } ->
          failwith "TODO"
      | Type { name; def } ->
          failwith "TODO"
      | _ -> failwith "Match error"
    ) (Ok with_names) tys
  in Ok processed

(* Entry point *)
let analyze_program (prg : Parsed.decl list) : env err =
  let env : env = Env.empty
  in let { types; excepts; values } = split_decls prg
  in let^ env = analyze_types env types
  in let^ env = analyze_excepts env excepts
  in analyze_values env values
