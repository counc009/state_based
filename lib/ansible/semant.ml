let ( let^ ) r f = Result.bind r f

module Context = Modules.Codegen

type 'a list2 = 'a Modules.Target.list2

module StringMap = Modules.Target.StringMap
module Target = Modules.Target.Ast_Target

(* The expected type of an expression *)
type etype =
  | Any
  | Num (* either an int or float *)
  | Int
  | Float
  | Bool
  | String
  | Path
  | Enum of string * (string * Target.typ) list2
  (* A single value or a list of values of some type. This is used for module
   * arguments which are lists but Ansible allows to be singleton values as
   * well *)
  | SingleOrList of etype
  | List of etype
  | Field of string * etype

(* The inferred type of an expression, this removes some placeholder types,
 * like Num and SingleOrList, but adds others that represent StringLike values
 * which can take on a myriad of types.
 * We also include an Equiv constructor that indicates the result of two
 * expresisons needing to have equal types and unifying their inferred types.
 * The inferred type (itype) is a reference because as we proceed through the
 * type checking/inference/unification process types of sub-expressions may be
 * refined. For instance, in the expression 3 < 3.2 we would initially infer
 * that the left-hand side has type Int but then after we determine that the
 * right-hand side has type Float we need to update the type of the left-hand
 * side to be Float as well. *)
type utype =
  | Int
  | Float
  | Bool
  | StringLike
  | String
  | Path
  | Enum of string * (string * Target.typ) list2
  | List of itype
  | Struct of itype StringMap.t
  | Equiv of itype
and itype = utype ref

class itype_stack =
object
  val mutable lst = ([] : itype list)
  method push x =
    lst <- x :: lst
  method elems = lst
end

(* For each variable we track the type that we infer for it, which is the
 * broadest type it can have based on the value assigned to it. We'll also
 * track all the uses of the variable which may allow us to refine the type
 * to be the broadest type of all its uses; this is important to allowing us
 * to determine when a variable is meant to be some enum value. *)
type var_type = { inferred : itype; uses : itype_stack }
type play_env = var_type StringMap.t

module Parsed = Ast.Parsed

module Typed = struct
  include Ast.Ast(struct
    type 'a anntd = 'a * itype
  end)

  let typeof (v : value) : itype =
    match v with
    | String (_, t) | Int (_, t) | Float (_, t) | Bool (_, t)
    | List (_, t) | Ident (_, t) | Unary (_, t) | Binary (_, t)
    | Dot (_, t) | VarDefined (_, t) | Fact (_, t) | Ternary (_, t)
    | Record (_, t) -> t
end

(* General utilities *)
let smap_map_res (f : 'a -> ('b, 'e) result) (m : 'a StringMap.t)
  : ('b StringMap.t, 'e) result =
  StringMap.fold (fun k x res ->
    let^ res = res
    in let^ y = f x
    in Ok (StringMap.add k y res))
    m (Ok StringMap.empty)

(* Utilities relating to types *)
(* Given an itype t returns the itype that t points to which is not an Equiv
 * note. Also updates all the intermediate pointers to point that itype, which
 * is effectively the path compression performed in the disjoint set data
 * structure *)
let rec simplify_itype (t : itype) : itype =
  match !t with
  | Equiv s ->
      let res = simplify_itype s
      in let () = t := Equiv res
      in res
  | _ -> t

(* Performs a deep copy of an itype *)
let rec dup_itype (t : itype) : itype =
  match !t with
  | Int -> ref Int
  | Float -> ref Float
  | Bool -> ref Bool
  | StringLike -> ref StringLike
  | String -> ref String
  | Path -> ref Path
  | Enum (nm, cs) -> ref (Enum (nm, cs))
  | List t -> ref (List (dup_itype t))
  | Struct ts -> ref (Struct (StringMap.map dup_itype ts))
  | Equiv t -> dup_itype t

let rec itype_of_etype (t : etype) : (itype, string) result =
  match t with
  | Any -> Error "Cannot infer concrete type of unknown type"
  | Num | Int -> Ok (ref Int)
  | Float -> Ok (ref Float)
  | Bool -> Ok (ref Bool)
  | String -> Ok (ref String)
  | Path -> Ok (ref Path)
  | Enum (nm, cs) -> Ok (ref (Enum (nm, cs)))
  | SingleOrList t | List t->
      let^ t' = itype_of_etype t in Ok (ref (List t'))
  | Field (f, t) ->
      let^ t' = itype_of_etype t
      in Ok (ref (Struct (StringMap.singleton f t')))

let rec string_of_etype (t : etype) : string =
  match t with
  | Any -> "any"
  | Num -> "number"
  | Int -> "int"
  | Float -> "float"
  | Bool -> "bool"
  | String -> "string"
  | Path -> "path"
  | Enum (nm, _) -> nm
  | SingleOrList t -> "singleton or list of " ^ string_of_etype t
  | List t -> "list of " ^ string_of_etype t
  | Field (f, t) -> "record with field " ^ f ^ " of type " ^ string_of_etype t

let rec string_of_itype (t : itype) : string =
  match !t with
  | Int -> "int"
  | Float -> "float"
  | Bool -> "bool"
  | StringLike -> "string-like value"
  | String -> "string"
  | Path -> "path"
  | Enum (nm, _) -> nm
  | List t -> "list of " ^ string_of_itype t
  | Struct fs -> "{ "
      ^ String.concat ", "
          (List.map (fun (f, t) -> f ^ ": " ^ string_of_itype t)
            (StringMap.to_list fs))
      ^ " }"
  | Equiv t -> string_of_itype t

(* Unification of two itypes. Returns whichever type is not reassigned to be
 * Equiv *)
let unify_types (_x : itype) (_y : itype) : (itype, string) result =
  Error "TODO"

(* Type-checking functions *)
let typecheck_value (v : Parsed.value) (t : etype) (_ctx : Context.context)
  (env : play_env) : (Typed.value, string) result =

  let rec check (v : Parsed.value) (t : etype) : (Typed.value, string) result =
    match v with
    | String s ->
        begin match t with
        | Any -> Ok (String (s, ref StringLike))
        | String -> Ok (String (s, ref String))
        | Path -> Ok (String (s, ref Path))
        | Enum (nm, cs) -> Ok (String (s, ref (Enum (nm, cs))))
        | SingleOrList t ->
            let^ res_t = check v t
            in Ok (Typed.List ([res_t], ref (List (Typed.typeof res_t))))
        | _ -> Error (Printf.sprintf
                        "Type error, found string-like value expected %s"
                        (string_of_etype t))
        end
    | Int i ->
        begin match t with
        | Any | Num | Int -> Ok (Int (i, ref Int))
        (* Coercions from int (and other primitive types) to other types is
         * handled by our code-generation. Because the type of this expression
         * could be changed elsewhere in the semantic analysis, we have to
         * handle such coercions there anyway *)
        | Float -> Ok (Int (i, ref Float))
        | String -> Ok (Int (i, ref String))
        | Path -> Ok (Int (i, ref Path))
        | SingleOrList t ->
            let^ res_t = check v t
            in Ok (Typed.List ([res_t], ref (List (Typed.typeof res_t))))
        | _ -> Error (Printf.sprintf
                        "Type error, found int value expected %s"
                        (string_of_etype t))
        end
    | Float f ->
        begin match t with
        | Any | Num | Float -> Ok (Float (f, ref Float))
        | String -> Ok (Float (f, ref String))
        | Path -> Ok (Float (f, ref Path))
        | SingleOrList t ->
            let^ res_t = check v t
            in Ok (Typed.List ([res_t], ref (List (Typed.typeof res_t))))
        | _ -> Error (Printf.sprintf
                        "Type error, found float value expected %s"
                        (string_of_etype t))
        end
    | Bool b ->
        begin match t with
        | Any | Bool -> Ok (Bool (b, ref Bool))
        | String -> Ok (Bool (b, ref String))
        | Path -> Ok (Bool (b, ref Path))
        | SingleOrList t ->
            let^ res_t = check v t
            in Ok (Typed.List ([res_t], ref (List (Typed.typeof res_t))))
        | _ -> Error (Printf.sprintf
                        "Type error, found bool value expected %s"
                        (string_of_etype t))
        end
    | List vs ->
        begin match t with
        | Any | SingleOrList _ | List _ ->
            let e_type =
              match t with
              | SingleOrList t | List t -> t
              | _ -> Any
            in let rec check_values (vs : Parsed.value list)
              : (Typed.value list * itype, string) result =
              match vs with
              | [] ->
                  let^ t = itype_of_etype e_type
                  in Ok ([], t)
              | [v] ->
                  let^ res_v = check v e_type
                  in Ok ([res_v], Typed.typeof res_v)
              | v :: vs ->
                  let^ res_v = check v e_type
                  in let typ_v = Typed.typeof res_v
                  in let^ (res_vs, typ_vs) = check_values vs
                  in let^ res_ty = unify_types typ_v typ_vs
                  in Ok (res_v :: res_vs, res_ty)
            in let^ (res_vs, elem_ty) = check_values vs
            in Ok (Typed.List (res_vs, ref (List (elem_ty))))
        | _ -> Error (Printf.sprintf
                        "Type error, found list value expected %s"
                        (string_of_etype t))
        end
    | Ident nm ->
        begin match StringMap.find_opt nm env with
        | None -> Error ("Undefined variable " ^ nm)
        | Some { inferred; uses } ->
            let rec compute_type (e : etype) (i : itype) =
              let i = simplify_itype i
              in match e, !i with
              | _, Equiv _ ->
                  failwith "Internal error, simplify_itype returned Equiv"

              | Any, _ -> Ok (dup_itype i)

              | Num, Int -> Ok (ref Int)
              | Num, Float -> Ok (ref Float)

              | Int, Int -> Ok (ref Int)

              | Float, Int | Float, Float -> Ok (ref Float)

              | Bool, Bool -> Ok (ref Bool)

              | String, Int | String, Float | String, Bool
                | String, StringLike | String, String | String, Path
                -> Ok (ref String)

              | Path, Int | Path, Float | Path, Bool
                | Path, StringLike | Path, String | Path, Path
                -> Ok (ref String)

              | Enum (n, cs), StringLike -> Ok (ref (Enum (n, cs)))
              | Enum (nt, _), Enum (ni, cs) when nt = ni
                -> Ok (ref (Enum (ni, cs)))

              | SingleOrList e, List t | List e, List t ->
                  let^ res_t = compute_type e t
                  in Ok (ref (List res_t))
              | SingleOrList e, _ ->
                  let^ res_t = compute_type e i
                  in Ok (ref (List res_t))

              | Field (f, e), Struct ts ->
                  begin match StringMap.find_opt f ts with
                  | None -> Error (Printf.sprintf "Type error, no field %s" f)
                  | Some t ->
                      let^ res_t = compute_type e t
                      in let ts = StringMap.map dup_itype ts
                      in let ts = StringMap.add f res_t ts
                      in Ok (ref (Struct ts))
                  end

              | Field (_, _), _
              | List _, _
              | Enum (_, _), _
              | Path, _
              | String, _
              | Bool, _
              | Float, _
              | Int, _
              | Num, _ ->
                  Error (Printf.sprintf
                            "Type error, found %s expected %s"
                            (string_of_itype inferred) (string_of_etype t))

            in let^ res_ty = compute_type t inferred
            in let () = uses#push res_ty
            in Ok (Typed.Ident (nm, res_ty))
        end
    | Unary (v, op) ->
        let^ (e_typ, res_typ) =
          let rec helper (t : etype)
            : (etype * (itype -> itype), string) result =
            match op with
            | Not ->
                begin match t with
                | Any | Bool -> Ok (Bool, dup_itype)
                | String -> Ok (Bool, fun _ -> ref String)
                | Path -> Ok (Bool, fun _ -> ref Path)
                | SingleOrList t ->
                    let^ (e_typ, res_typ) = helper t
                    in Ok (e_typ, fun t -> ref (List (res_typ t)))
                | _ ->
                    Error (Printf.sprintf
                            "Type error, found bool expected %s"
                            (string_of_etype t))
                end
            | Lower ->
                begin match t with
                | Any | String -> Ok (String, dup_itype)
                | Path -> Ok (String, fun _ -> ref Path)
                | SingleOrList t ->
                    let^ (e_typ, res_typ) = helper t
                    in Ok (e_typ, fun t -> ref (List (res_typ t)))
                | _ ->
                    Error (Printf.sprintf
                            "Type error, found string expected %s"
                            (string_of_etype t))
                end
            | Neg ->
                begin match t with
                | Any | Num -> Ok (Num, dup_itype)
                | Int -> Ok (Int, dup_itype)
                | Float -> Ok (Float, dup_itype)
                | String -> Ok (Num, fun _ -> ref String)
                | Path -> Ok (Num, fun _ -> ref Path)
                | SingleOrList t ->
                    let^ (e_typ, res_typ) = helper t
                    in Ok (e_typ, fun t -> ref (List (res_typ t)))
                | _ ->
                    Error (Printf.sprintf
                            "Type error, found number expected %s"
                            (string_of_etype t))
                end
          in helper t
        in let^ res_v = check v e_typ
        in Ok (Typed.Unary ((res_v, op), res_typ (Typed.typeof res_v)))
    (* The challenge is still when do we re-use the type of the sub-expression
     * and when do we generate a new type for it?
     * For instance, my instinct says that 3 + 2 should give 3, 2, and the
     * whole expression the exact same type and so if we then have the
     * expression 3 + 2 < 3.14 then we can coerce all of the sub-expressions to
     * floats. But, if instead we have (3 + 2) == "hello" we need to coerce
     * just the 3 + 2 sub-expression to string, not its sub-expressions. *)
    | _ -> Error "TODO"

  in check v t
