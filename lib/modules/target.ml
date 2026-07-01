open Calculus.Ast

let ( let* ) = Option.bind

(* A 'a list2 is a list with at least two elements *)
type 'a list2 = LastTwo of 'a * 'a | Cons of 'a * 'a list2
type 'a list' = Nil | Singleton of 'a | List of 'a list2

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type 't prims   = Unit | Bool | Int | Float | String | Path | StringSet
                | Exc of 't StringMap.t
type 't constr  = List of 't | Option of 't
                (* For all other enums we store the name of the enum and the
                 * name of each constructor *)
                | Cases          of string * (string * 't) list2
type 't func    = Proj           of bool * 't * 't   (* true = 1, false = 2 *)
                | Constructor    of bool * 't constr (* true = L, false = R *)
                | EmptyStruct    of 't StringMap.t
                | AddField       of 't StringMap.t * string
                | ReadField      of 't StringMap.t * string
                | GenUniversal   of 't
                | GenExistential of 't
                | BoolNeg
                | BoolOr
                | BoolAnd
                | Concat
                | ConcatLine
                | ContainsLine
                | RemoveLastLine
                | Equal          of 't
                | Append         of 't (* Type of list elements *)
                | ListLength     of 't (* Type of list elements *)
                | AddInt
                | AddFloat
                | SubInt
                | SubFloat
                | MulInt
                | MulFloat
                | DivInt
                | DivFloat
                | Modulo
                | Power
                | LShift
                | RShift
                | LtInt
                | LtFloat
                | LeInt
                | LeFloat
                | ToLower
                | Substring
                | StringSubst
                | StringOfInt
                | StringOfFloat
                | StringOfBool
                | FloatOfInt
                (* Path operations *)
                | ConsPath
                | PathOfString
                | StringOfPath
                | EndsWithDir
                | BaseName
                | PathFrom
                | AddExt
                | NormalizePath
                (* Regular Expression Operations *)
                | RegexOfLiteral
                | RemoveMatchingLines
                | ReplaceLastMatchingExpand
                | ReplaceLastMatching
                | InsertNearMatching
                | RegexLineMatches
                | GetLastLineMatch
                (* Operations related to marked blocks (i.e., blockinfile) *)
                | FindBlock
                | RemoveBlock
                | ReplaceBlock
                (* Functions for Ansible *)
                | CanBecome
                | HostIncluded
                (* Exception functions: generating and unpacking *)
                | GenExcept of 't StringMap.t * string
                | UnpackExcept of 't StringMap.t * string
                (* String sets *)
                | SetAdd
                | SetContains
                (* Name and input and output types *)
                | Uninterpreted of string * 't * 't
type ('v, 't) lit = Unit    of unit
                  | Bool    of bool
                  | Int     of int
                  | Float   of float
                  | String  of string
                  | Path    of string
                  | StringSet of StringSet.t
                  | Except  of 't StringMap.t * string * 'v

let home_regex = Re.compile (Re.Perl.re {|^~([^/]*)|})
let regex_special = Re.compile (Re.Posix.re {|[.^$*+?{}()\\[]|]|})

let pattern_regex = Re.compile (
  Re.seq [
    Re.char '\\';
    Re.alt [
      Re.group (Re.rep1 (Re.rg '0' '9'));
      Re.seq [
        Re.str "g<";
        Re.group (Re.rep1 (Re.rg '0' '9'));
        Re.str ">" ] ] ])
let subst_pattern (pat : string) (g : Re.Group.t) : string =
  let subst (n : Re.Group.t) : string =
    let i =
      if Re.Group.test n 1
      then Some 1
      else if Re.Group.test n 2
      then Some 2
      else None
    in match i with
    | None -> Re.Group.get n 0
    | Some i ->
        match int_of_string_opt (Re.Group.get n i) with
        | None -> Re.Group.get n 0
        | Some i ->
            if Re.Group.test g i
            then Re.Group.get g i
            else "%%UNDEFINED%%"
  in Re.replace pattern_regex ~f:subst pat

let rec update_first (f : 'a -> 'a option) (xs : 'a list) : 'a list =
  match xs with
  | [] -> []
  | x :: xs ->
      match f x with
      | Some x -> x :: xs
      | None -> x :: update_first f xs

let update_last (f : 'a -> 'a option) (xs : 'a list) : 'a list =
  let rec update (xs : 'a list) : 'a list * bool =
    match xs with
    | [] -> ([], false)
    | x :: xs ->
        let (xs, updated) = update xs
        in if updated then (x :: xs, true)
        else
          let (x, updated) =
            match f x with
            | None -> (x, false)
            | Some x -> (x, true)
          in (x :: xs, updated)
  in fst (update xs)

module rec Ast_Target : Ast_Defs
  with type variable  = string
  with type field     = string
  with type primTy    = Ast_Target.typ prims
  with type namedTy   = Ast_Target.typ constr
  with type structTy  = Ast_Target.typ StringMap.t
  with type funct     = Ast_Target.typ func
  with type literal   = (Ast_Target.value, Ast_Target.typ) lit
  with type attribute = string * Ast_Target.typ
  with type element   = string * Ast_Target.typ
  with type action    = string * Ast_Target.typ * Ast_Target.typ
                      * Ast_Target.stmt option ref
= struct
  type field = string
  module FieldMap = StringMap

  type primTy  = typ prims
  and  namedTy = typ constr
  and structTy = typ FieldMap.t
  and typ = Product    of typ * typ
          | Primitive  of primTy
          | Named      of namedTy
          | Struct     of structTy

  type funct = typ func

  type variable = string
  module VariableMap = StringMap

  type literal = (value, typ) lit
   and record = value FieldMap.t
   and value = Unknown      of id * typ
             | Literal      of literal * primTy
             | Function     of funct * value * typ
             | Pair         of value * value * typ
             | Constructor  of namedTy * bool * value
             | Struct       of structTy * record
             | ListVal      of namedTy * value

  type attribute = string * typ
  type element = string * typ

  type expr = Function  of funct * expr
            | Literal   of literal
            | Variable  of variable
            | Pair      of expr * expr

  type qual = Attribute   of attribute * expr
            | Element     of element * expr * qual option
            | NotElement  of element * expr
  type attr = AttrAccess  of attribute
            | OnElement   of element * expr * attr
  type elem = Element     of element * expr
            | OnElement   of element * expr * elem

  type action = string * typ * typ * stmt option ref
   and stmt = Seq      of stmt * stmt
            | Action   of variable * action * expr
            | Assign   of variable * expr
            | Add      of qual
            | Get      of variable * attr
            | Contains of elem * stmt * stmt
            | Cond     of expr * stmt * stmt
            | Match    of expr * variable * stmt * stmt
            | ForEach  of variable * typ * expr * variable * stmt
            | TryCatch of stmt * variable * stmt * stmt
            | Localize of element * expr * stmt
            | Raise    of expr
            | Return   of expr
            | Yield    of expr
            | Pass

  let rec typeEq x y =
    match x, y with
    | Primitive x, Primitive y -> x = y
    | Product (x1, x2), Product (y1, y2) -> typeEq x1 y1 && typeEq x2 y2
    | Named (List x), Named (List y) -> typeEq x y
    | Named (Option x), Named (Option y) -> typeEq x y
    | Named (Cases (xn, xs)), Named (Cases (yn, ys)) when xn = yn ->
        let rec list2_eq xs ys =
          match xs, ys with
          | LastTwo ((xn1, x1), (xn2, x2)), LastTwo ((yn1, y1), (yn2, y2)) ->
              xn1 = yn1 && xn2 = yn2 && typeEq x1 y1 && typeEq x2 y2
          | Cons ((xn, x), xs), Cons ((yn, y), ys) ->
              xn = yn && typeEq x y && list2_eq xs ys
          | _, _  -> false
        in list2_eq xs ys
    | Struct xs, Struct ys -> StringMap.equal typeEq xs ys
    | _, _ -> false

  type values_equal_res = Yes | No | Unsure
  let rec values_equal x y : values_equal_res =
    match x, y with
    | Unknown (x, _), Unknown (y, _) -> if x = y then Yes else Unsure
    | Unknown (_, _), _ | _, Unknown (_, _) -> Unsure

    | Literal (x, _), Literal (y, _) -> if x = y then Yes else No

    | Function (fx, vx, _), Function (fy, vy, _) when fx = fy ->
        begin match values_equal vx vy with
        | Yes -> Yes
        | _ -> Unsure
        end
    | Function (_, _, _), _ | _, Function (_, _, _) -> Unsure

    | Pair (xa, xb, _), Pair (ya, yb, _) ->
        begin match values_equal xa ya, values_equal xb yb with
        | No, _ | _, No -> No
        | Unsure, _ | _, Unsure -> Unsure
        | Yes, Yes -> Yes
        end

    | Constructor (_, cx, vx), Constructor (_, cy, vy) ->
        if cx <> cy then No else values_equal vx vy

    | Struct (_, xs), Struct (_, ys) ->
        (* Collect the bindings where xs and ys are not (necessarily) equal
         * (possibly because only one of them defines it) *)
        let diffs =
          FieldMap.merge (fun _ x_val y_val ->
            match x_val, y_val with
            | Some x, Some y ->
                begin match values_equal x y with
                | Yes -> None
                | Unsure -> Some Unsure
                | No -> Some No
                end
            | _, _ -> Some No)
            xs ys
        in if FieldMap.is_empty diffs
        then Yes (* nothing in the diffs means all bindings are equal *)
        else if FieldMap.exists (fun _ v -> v = No) diffs
        then No
        else Unsure

    | ListVal (_, vx), ListVal (_, vy) -> values_equal vx vy

    | ListVal (_, _), Constructor (_, _, _)
    | Constructor (_, _, _), ListVal (_, _) -> Unsure

    | Literal (_, _), Pair (_, _, _)
    | Literal (_, _), Constructor (_, _, _)
    | Literal (_, _), Struct (_, _)
    | Literal (_, _), ListVal (_, _)
    | Pair (_, _, _), Literal (_, _)
    | Pair (_, _, _), Constructor (_, _, _)
    | Pair (_, _, _), Struct (_, _)
    | Pair (_, _, _), ListVal (_, _)
    | Constructor (_, _, _), Literal (_, _)
    | Constructor (_, _, _), Pair (_, _, _)
    | Constructor (_, _, _), Struct (_, _)
    | Struct (_, _), Literal (_, _)
    | Struct (_, _), Pair (_, _, _)
    | Struct (_, _), Constructor (_, _, _)
    | Struct (_, _), ListVal (_, _)
    | ListVal (_, _), Literal (_, _)
    | ListVal (_, _), Pair (_, _, _)
    | ListVal (_, _), Struct (_, _) ->
        failwith "Attempted to compare values that are of different types"

  let rec append_lists et x y : value =
    match x with
    | Constructor (_, true, _) -> (* Nil *) y
    | Constructor (listTy, false, Pair(hd, tl, pairTy)) ->
        Constructor (listTy, false, Pair (hd, append_lists et tl y, pairTy))
    | _ -> Function (Append et, Pair (x, y, Product (et, Named (List et))), Named (List et))

  let list_length v : value eval =
    let rec len (v : value) : int option =
      match v with
      | Constructor (_, true, _) -> (* Nil *) Some 0
      | Constructor (_, false, Pair (_, tl, _)) ->
          begin match len tl with
          | None -> None
          | Some n -> Some (n + 1)
          end
      | _ -> None
    in match len v with
    | Some n -> Reduced (Literal (Int n, Int))
    | None -> Stuck

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))
    | Option t -> (Primitive Unit, t)
    | Cases (_, LastTwo ((_, s), (_, t))) -> (s, t)
    | Cases (nm, Cons ((_, s), ts)) -> (s, Named (Cases (nm, ts)))
  let structTyDef fs = fs

  let regex_replace : Re.re = Re.compile (Re.Posix.re {|\\[sS]|})

  let compile_regex (s : string) : Re.re option =
    let replace_special (g : Re.Group.t) : string =
      match Re.Group.get g 0 with
      | "\\s" -> "[ \t\n\r]"
      | "\\S" -> "[^ \t\n\r]"
      | _ -> failwith "Error in compiling regex"
    in try 
      Some (
        Re.compile (
          Re.Posix.re (Re.replace regex_replace ~f:replace_special s)))
    with Re.Posix.Parse_error ->
      None

  let funcDef = function
    | Proj (true, s, t)  -> (Product (s, t), s,
                             fun (v : value) ->
                               match v with Pair (x, _, _) -> Reduced x
                                          | _ -> Stuck)
    | Proj (false, s, t) -> (Product (s, t), t,
                             fun (v : value) ->
                               match v with Pair (_, y, _) -> Reduced y
                                          | _ -> Stuck)
    | Constructor (true, n)  -> (fst (namedTyDef n), Named n,
                                 fun v -> Reduced (Constructor (n, true, v)))
    | Constructor (false, n) -> (snd (namedTyDef n), Named n,
                                 fun v -> Reduced (Constructor (n, false, v)))
    | EmptyStruct s -> (Primitive Unit, Struct s,
                        fun _ -> Reduced (Struct (s, FieldMap.empty)))
    | AddField (s, f) -> (Product (Struct s, FieldMap.find f (structTyDef s)),
                          Struct s,
                          fun v -> match v with Pair (Struct (_, fs), x, _)
                                    -> Reduced (Struct (s, FieldMap.add f x fs))
                                   | _ -> Stuck)
    | ReadField (s, f) -> (Struct s, FieldMap.find f (structTyDef s),
                           fun v -> match v with Struct (_, fs)
                                    -> begin match FieldMap.find_opt f fs with
                                       | Some x -> Reduced x
                                       | None -> Err ("Missing field " ^ f)
                                       end
                                    | _ -> Stuck)
    | GenUniversal t -> (Primitive Unit, t,
                          fun _ -> Reduced (Unknown (Universal (uid ()), t)))
    | GenExistential t -> (Primitive Unit, t,
                          fun _ -> Reduced (Unknown (Existential (uid ()), t)))
    | BoolNeg -> (Primitive Bool, Primitive Bool,
        fun v -> match v with Literal (Bool b, _)
                    -> Reduced (Literal (Bool (not b), Bool))
                 | _ -> Stuck)
    | BoolOr -> (Product (Primitive Bool, Primitive Bool), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Bool x, _), Literal (Bool y, _), _)
              -> Reduced (Literal (Bool (x || y), Bool))
          | _ -> Stuck)
    | BoolAnd -> (Product (Primitive Bool, Primitive Bool), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Bool x, _), Literal (Bool y, _), _)
              -> Reduced (Literal (Bool (x && y), Bool))
          | _ -> Stuck)
    | Concat -> (Product (Primitive String, Primitive String),
                 Primitive String,
        fun v -> match v with
          | Pair (Literal (String p, _), Literal (String q, _), _)
            -> Reduced (Literal (String (p ^ q), String))
          | Pair (Literal (String "", _), q, _) -> Reduced q
          | Pair (p, Literal (String "", _), _) -> Reduced p
          | _ -> Stuck)
    | ConcatLine -> (Product (Primitive String, Primitive String),
                     Primitive String,
        fun v -> match v with
        | Pair (Literal (String p, _), Literal (String q, _), _) ->
            let p =
              if p = "" || String.ends_with ~suffix:"\n" p
              then p
              else p ^ "\n"
            in let q =
              if q = "" || String.ends_with ~suffix:"\n" q
              then q
              else q ^ "\n"
            in Reduced (Literal (String (p ^ q), String))
        | Pair (Literal (String "", _), q, _) -> Reduced q
        | Pair (p, Literal (String "", _), _) -> Reduced p
        | _ -> Stuck)
    | ContainsLine -> (Product (Primitive String, Primitive String),
        Primitive Bool,
        fun v -> match v with
        | Pair (Literal (String line, _), Literal (String text, _), _) ->
            let res =
              String.starts_with ~prefix:(line ^ "\n") text
              || String.ends_with ~suffix:("\n" ^ line) text
              || line = text
              || String.includes ~affix:("\n" ^ line ^ "\n") text
            in Reduced (Literal (Bool res, Bool))
        | _ -> Stuck)
    | RemoveLastLine -> (Primitive String, Primitive String,
        fun v -> match v with
        | Literal (String s, _) ->
            let lines = String.split_on_char '\n' s
            in let rec front (xs : 'a list) : 'a list =
              match xs with
              | [] | [_] -> []
              | x :: xs -> x :: front xs
            in let new_lines = front lines
            in let new_s = String.concat "\n" new_lines
            in Reduced (Literal (String new_s, String))
        | _ -> Stuck)
    | Equal t -> (Product (t, t), Primitive Bool,
        fun v -> match v with
          | Pair (x, y, _) ->
              begin match values_equal x y with
              | Yes -> Reduced (Literal (Bool true, Bool))
              | No  -> Reduced (Literal (Bool false, Bool))
              | Unsure -> Stuck
              end
          | _ -> Stuck)
    | Append et -> (Product (Named (List et), Named (List et)), Named (List et),
        fun v -> match v with
          | Pair (x, y, _) -> Reduced (append_lists et x y)
          | _ -> Stuck)
    | ListLength et -> (Named (List et), Primitive Int, list_length)
    | AddInt -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (x + y), Int))
          | Pair (Literal (Int 0, _), y, _) -> Reduced y
          | Pair (x, Literal (Int 0, _), _) -> Reduced x
          | _ -> Stuck)
    | AddFloat -> (Product (Primitive Float, Primitive Float), Primitive Float,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Float (x +. y), Float))
          | Pair (Literal (Float 0.0, _), y, _) -> Reduced y
          | Pair (x, Literal (Float 0.0, _), _) -> Reduced x
          | _ -> Stuck)
    | SubInt -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (x - y), Int))
          | Pair (x, Literal (Int 0, _), _) -> Reduced x
          | _ -> Stuck)
    | SubFloat -> (Product (Primitive Float, Primitive Float), Primitive Float,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Float (x -. y), Float))
          | Pair (x, Literal (Float 0.0, _), _) -> Reduced x
          | _ -> Stuck)
    | MulInt -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (x * y), Int))
          | Pair (Literal (Int 0, _), _, _) -> Reduced (Literal (Int 0, Int))
          | Pair (_, Literal (Int 0, _), _) -> Reduced (Literal (Int 0, Int))
          | _ -> Stuck)
    | MulFloat -> (Product (Primitive Float, Primitive Float), Primitive Float,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Float (x *. y), Float))
          | Pair (Literal (Float 0.0, _), _, _) ->
              Reduced (Literal (Float 0.0, Int))
          | Pair (_, Literal (Float 0.0, _), _) ->
              Reduced (Literal (Float 0.0, Int))
          | _ -> Stuck)
    | DivInt -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (_, Literal (Int 0, _), _) -> Err "Division by 0"
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (x / y), Int))
          | _ -> Stuck)
    | DivFloat -> (Product (Primitive Float, Primitive Float), Primitive Float,
        fun v -> match v with
          | Pair (_, Literal (Float 0.0, _), _) -> Err "Division by 0"
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Float (x /. y), Float))
          | _ -> Stuck)
    | Modulo -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (_, Literal (Int 0, _), _) -> Err "Modulo by 0"
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (x mod y), Int))
          | _ -> Stuck)
    | Power -> (Product (Primitive Float, Primitive Float), Primitive Float,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Float (Float.pow x y), Float))
          | _ -> Stuck)
    | LShift -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (_, Literal (Int y, _), _) when y < 0
              -> Err "Shift by negative number"
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (Int.shift_left x y), Int))
          | Pair (x, Literal (Int 0, _), _) -> Reduced x
          | Pair (Literal (Int 0, _), _, _) -> Reduced (Literal (Int 0, Int))
          | _ -> Stuck)
    | RShift -> (Product (Primitive Int, Primitive Int), Primitive Int,
        fun v -> match v with
          | Pair (_, Literal (Int y, _), _) when y < 0
              -> Err "Shift by negative number"
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Int (Int.shift_right x y), Int))
          | Pair (x, Literal (Int 0, _), _) -> Reduced x
          | Pair (Literal (Int 0, _), _, _) -> Reduced (Literal (Int 0, Int))
          | _ -> Stuck)
    | LtInt -> (Product (Primitive Int, Primitive Int), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Bool (x < y), Bool))
          | _ -> Stuck)
    | LtFloat -> (Product (Primitive Float, Primitive Float), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Bool (x < y), Bool))
          | _ -> Stuck)
    | LeInt -> (Product (Primitive Int, Primitive Int), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Int x, _), Literal (Int y, _), _)
              -> Reduced (Literal (Bool (x <= y), Bool))
          | _ -> Stuck)
    | LeFloat -> (Product (Primitive Float, Primitive Float), Primitive Bool,
        fun v -> match v with
          | Pair (Literal (Float x, _), Literal (Float y, _), _)
              -> Reduced (Literal (Bool (x <= y), Bool))
          | _ -> Stuck)
    | ToLower -> (Primitive String, Primitive String,
        fun v -> match v with
          | Literal (String s, _) ->
              Reduced (Literal (String (String.lowercase_ascii s), String))
          | _ -> Stuck)
    | Substring -> (Product (Primitive String,
                      Product (Primitive Int, Primitive Int)),
                    Primitive String,
        fun v -> match v with
        | Pair (Literal (String s, _),
            Pair (Literal (Int i, _), Literal (Int j, _), _), _) ->
              begin try
                Reduced (Literal (String (String.sub s i j), String))
              with Invalid_argument _ ->
                Reduced (Literal (String "", String))
              end
        | _ -> Stuck)
    | StringSubst -> (Product (Primitive String,
                        Product (Primitive String, Primitive String)),
                      Primitive String,
        fun v -> match v with
        | Pair (Literal (String str, _),
            Pair (Literal (String pat, _), Literal (String repr, _), _), _) ->
              Reduced (Literal (String (
                String.replace_all ~sub:pat ~by:repr str), String))
        | _ -> Stuck)
    | StringOfInt -> (Primitive Int, Primitive String,
        fun v -> match v with
          | Literal (Int x, _) ->
              Reduced (Literal (String (string_of_int x), String))
          | _ -> Stuck)
    | StringOfFloat -> (Primitive Float, Primitive String,
        fun v -> match v with
          | Literal (Float x, _) ->
              Reduced (Literal (String (string_of_float x), String))
          | _ -> Stuck)
    | StringOfBool -> (Primitive Bool, Primitive String,
        fun v -> match v with
          | Literal (Bool x, _) ->
              Reduced (Literal (String (string_of_bool x), String))
          | _ -> Stuck)
    | FloatOfInt -> (Primitive Int, Primitive Float,
        fun v -> match v with
          | Literal (Int x, _) ->
              Reduced (Literal (Float (float_of_int x), Float))
          | _ -> Stuck)
    | ConsPath -> (Product (Primitive Path, Primitive Path),
                   Primitive Path,
        let rec process (v : value) : value eval =
          match v with
          | Pair (Literal (Path p, _), Literal (Path q, _), _)
            -> if String.ends_with ~suffix:"/" p
               then Reduced (Literal (Path (p ^ q), Path))
               else Reduced (Literal (Path (p ^ "/" ^ q), Path))
          | Pair (Function (ConsPath, Pair (x, y, t), _), z, _) ->
              begin match process (Pair (y, z, t)) with
              | Err msg -> Err msg
              | Reduced rhs ->
                  Reduced (Function (ConsPath, Pair (x, rhs, t),
                    Primitive Path))
              | Stuck ->
                  Reduced (Function (ConsPath, Pair (x,
                    Function (ConsPath, Pair (y, z, t), Primitive Path), t),
                    Primitive Path))
              end
          | _ -> Stuck
        in process)
    | PathOfString -> (Primitive String, Primitive Path,
        fun v -> match v with
          | Literal (String s, _) -> Reduced (Literal (Path s, Path))
          | Function (Concat, Pair (Literal (String p, _), q, _), _) ->
              if String.ends_with ~suffix:"/" p
              then
                Reduced (Function (ConsPath, 
                  Pair (Literal (Path p, Path),
                    Function (PathOfString, q, Primitive Path),
                    Product (Primitive Path, Primitive Path)), Primitive Path))
              else Stuck
          | Function (StringOfPath, p, _) -> Reduced p
          | _ -> Stuck)
    | StringOfPath -> (Primitive Path, Primitive String,
        fun v -> match v with
          | Literal (Path s, _) -> Reduced (Literal (String s, String))
          | Function (PathOfString, s, _) -> Reduced s
          | _ -> Stuck)
    | EndsWithDir -> (Primitive Path, Primitive Bool,
        fun v -> match v with
          | Literal (Path p, _)
            -> let lastChar = String.sub p (String.length p - 1) 1
               in let res = lastChar = "/"
               in Reduced (Literal (Bool res, Bool))
          | _ -> Stuck)
    | BaseName -> (Primitive Path, Primitive Path,
        fun v -> match v with
          | Literal (Path p, _)
            -> Reduced (Literal (Path (Filename.basename p), Path))
          | _ -> Stuck)
    | PathFrom -> (Product (Primitive Path, Primitive Path),
                   Primitive Path,
        fun v -> match v with
          | Pair (Literal (Path base, _), Literal (Path full, _), _)
            -> if String.sub full 0 (String.length base) = base
               then
                 let res = String.sub full (String.length base) (String.length full - String.length base)
                 in Reduced (Literal (Path res, Path))
               else Err "The base path in path_from must be the base of the full path"
          | _ -> Stuck)
    | AddExt -> (Product (Primitive Path, Primitive String),
                 Primitive Path,
        fun v -> match v with
          | Pair (Literal (Path base, _), Literal (String ext, _), _)
            -> Reduced (Literal (Path (base ^ ext), Path))
          | _ -> Stuck)
    (* Path normalization removes 1) any / at the end of the path
     *                            2) ~name becomes /home/name
     * there are probably other things we could/should add, but these are the
     * ones I need immediately *)
    | NormalizePath -> (Primitive Path, Primitive Path,
        fun v -> match v with
        | Literal (Path p, _)
          -> let lastChar = String.sub p (String.length p - 1) 1
             in let normLast = 
               if lastChar = "/" then String.sub p 0 (String.length p - 1)
                                 else p
             in let normHome =
               Re.replace home_regex ~f:(fun g -> "/home/" ^ Re.Group.get g 1)
                normLast
             in Reduced (Literal (Path normHome, Path))
        (* Normalization of a normalized path is just the same *)
        | Function (NormalizePath, p, _) ->
            Reduced (Function (NormalizePath, p, Primitive Path))
        | _ -> Stuck)
    | RegexOfLiteral -> (Primitive String, Primitive String,
        fun v -> match v with
        | Literal (String s, _) ->
            let new_s =
              Re.replace regex_special ~f:(fun g -> "\\" ^ Re.Group.get g 0) s
            in Reduced (Literal (String new_s, String))
        | _ -> Stuck )
    | RemoveMatchingLines -> (Product (Primitive String, Primitive String),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String regex, _), Literal (String body, _), _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regex ->
                let lines = String.split_on_char '\n' body
                in let new_lines =
                  List.filter (fun s -> not (Re.execp regex s)) lines
                in let new_s = String.concat "\n" new_lines
                in Reduced (Literal (String new_s, String))
            end
        | _ -> Stuck)
    | ReplaceLastMatchingExpand -> (
      Product (Primitive String, Product (Primitive String, Primitive String)),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String regex, _),
            Pair (Literal (String line, _),
              Literal (String body, _), _), _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regex ->
                let lines = String.split_on_char '\n' body
                in let update_line (l : string) =
                  match Re.exec_opt regex l with
                  | None -> None
                  | Some g -> Some (subst_pattern line g)
                in let new_lines = update_last update_line lines
                in let new_s = String.concat "\n" new_lines
                in Reduced (Literal (String new_s, String))
            end
        | _ -> Stuck)
    | ReplaceLastMatching -> (
      Product (Primitive String, Product (Primitive String, Primitive String)),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String regex, _),
            Pair (Literal (String line, _),
              Literal (String body, _), _), _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regex ->
                let lines = String.split_on_char '\n' body
                in let update_line (l : string) =
                  if Re.execp regex l
                  then Some line
                  else None
                in let new_lines = update_last update_line lines
                in let new_s = String.concat "\n" new_lines
                in Reduced (Literal (String new_s, String))
            end
        | _ -> Stuck)
    | InsertNearMatching -> (
        Product (
          Named (Cases ("insert_loc",
            Cons (("before_first", Primitive Unit),
            Cons (("before_last", Primitive Unit),
            LastTwo (("after_first", Primitive Unit),
              ("after_last", Primitive Unit)))))),
          Product (Primitive String,
          Product (Primitive String, Primitive String))),
        Primitive String,
        fun v -> match v with
        | Pair (loc,
            Pair (Literal (String regex, _),
              Pair (Literal (String line, _),
                Literal (String body, _), _), _), _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regex ->
                let lines = String.split_on_char '\n' body
                in begin match loc with
                (* before_first *)
                | Constructor (_, true, _) ->
                    let update_line (l : string) =
                      if Re.execp regex l
                      then Some (line ^ "\n" ^ l)
                      else None
                    in let new_lines = update_first update_line lines
                    in let new_s = String.concat "\n" new_lines
                    in Reduced (Literal (String new_s, String))
                (* before_last *)
                | Constructor (_, false, Constructor (_, true, _)) ->
                    let update_line (l : string) =
                      if Re.execp regex l
                      then Some (line ^ "\n" ^ l)
                      else None
                    in let new_lines = update_last update_line lines
                    in let new_s = String.concat "\n" new_lines
                    in Reduced (Literal (String new_s, String))
                (* after_first *)
                | Constructor (_, false, Constructor (_, false, Constructor (_, true, _))) ->
                    let update_line (l : string) =
                      if Re.execp regex l
                      then Some (l ^ "\n" ^ line)
                      else None
                    in let new_lines = update_first update_line lines
                    in let new_s = String.concat "\n" new_lines
                    in Reduced (Literal (String new_s, String))
                (* after_last *)
                | Constructor (_, false, Constructor (_, false, Constructor (_, false, _))) ->
                    let update_line (l : string) =
                      if Re.execp regex l
                      then Some (l ^ "\n" ^ line)
                      else None
                    in let new_lines = update_last update_line lines
                    in let new_s = String.concat "\n" new_lines
                    in Reduced (Literal (String new_s, String))
                | _ -> Stuck
                end
            end
        | _ -> Stuck)
    | RegexLineMatches -> (Product (Primitive String, Primitive String),
        Primitive Bool,
        fun v -> match v with
        | Pair (Literal (String regex, _), body, _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regexp ->
                let rec compute : value -> value eval = function
                  | Literal (String body, _) ->
                      let lines = String.split_on_char '\n' body
                      in let matched = List.exists (Re.execp regexp) lines
                      in Reduced (Literal (Bool matched, Bool))
                  | Function (ConcatLine, Pair (x, y, _), _) ->
                      begin match compute x, compute y with
                      | Reduced (Literal (Bool true, _)), _ 
                      | _, Reduced (Literal (Bool true, _)) ->
                          Reduced (Literal (Bool true, Bool))
                      | Reduced (Literal (Bool false, _)),
                        Reduced (Literal (Bool false, _)) ->
                          Reduced (Literal (Bool false, Bool))
                      | _, _ -> Stuck
                      end
                  | Function (RemoveMatchingLines,
                      Pair (Literal (String remregex, _), _, _), _) ->
                      if remregex = regex || remregex = regex ^ ".*"
                          || remregex = regex ^ ".*$"
                      then Reduced (Literal (Bool false, Bool))
                      else Stuck
                  | Function (ReplaceLastMatching,
                      Pair (Literal (String upregex, _),
                        Pair (Literal (String line, _), _, _), _), _) ->
                      if upregex = regex || upregex = regex ^ ".*"
                          || upregex = regex ^ ".*$"
                      then
                        if Re.execp regexp line
                        then Reduced (Literal (Bool true, Bool))
                        else Stuck
                      else Stuck
                  | Function (InsertNearMatching,
                      Pair (_, Pair (_, Pair (line, body, _), _), _), _) ->
                      begin match compute line, compute body with
                      | Reduced (Literal (Bool true, _)), _ 
                      | _, Reduced (Literal (Bool true, _)) ->
                          Reduced (Literal (Bool true, Bool))
                      | Reduced (Literal (Bool false, _)),
                        Reduced (Literal (Bool false, _)) ->
                          Reduced (Literal (Bool false, Bool))
                      | _, _ -> Stuck
                      end
                  | _ -> Stuck
                in compute body
            end
        | _ -> Stuck)
    | GetLastLineMatch -> (Product (Primitive String, Primitive String),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String regex, _), body, _) ->
            begin match compile_regex regex with
            | None -> Err "Invalid regex"
            | Some regexp ->
                let rec compute : value -> value eval = function
                  | Literal (String body, _) ->
                      let lines = String.split_on_char '\n' body
                      in begin match List.find_opt (Re.execp regexp) lines with
                      | None -> Err "No matching line"
                      | Some l -> Reduced (Literal (String l, String))
                      end
                  | Function (ConcatLine, Pair (x, y, _), _) ->
                      begin match compute y with
                      | Reduced res -> Reduced res
                      | Err "No matching line" -> compute x
                      | _ -> Stuck
                      end
                  | Function (RemoveMatchingLines,
                      Pair (Literal (String remregex, _), _, _), _) ->
                      if remregex = regex || remregex = regex ^ ".*"
                          || remregex = regex ^ ".*$"
                      then Err "No matching line"
                      else Stuck
                  | Function (ReplaceLastMatching,
                      Pair (Literal (String upregex, _),
                        Pair (Literal (String line, _), _, _), _), _) ->
                      if upregex = regex || upregex = regex ^ ".*"
                          || upregex = regex ^ ".*$"
                      then
                        if Re.execp regexp line
                        then Reduced (Literal (String line, String))
                        else Stuck
                      else Stuck
                  | Function (InsertNearMatching,
                      Pair (
                        Constructor (_, false,
                          Constructor (_, false,
                            Constructor (_, false, _))),
                        Pair (Literal (String sregex, _),
                          Pair (Literal (String line, _), _, _), _), _), _) ->
                      if sregex = regex || sregex = regex ^ ".*"
                          || sregex = regex ^ ".*$"
                      then
                        if Re.execp regexp line
                        then Reduced (Literal (String line, String))
                        else Stuck
                      else Stuck
                  | _ -> Stuck
                in compute body
            end
        | _ -> Stuck)
    | FindBlock -> (Product (Primitive String,
                      Product (Primitive String, Primitive String)),
        Primitive Bool,
        fun v -> match v with
        | Pair (Literal (String begin_line, _),
            Pair (Literal (String end_line, _),
              Literal (String content, _), _), _) ->
            let res =
              let* idx_start =
                if String.starts_with ~prefix:(begin_line ^ "\n") content
                then Some 0
                else String.find_first ~sub:("\n" ^ begin_line ^ "\n") content
              in match String.find_first ~sub:("\n" ^ end_line ^ "\n")
                        ~start:idx_start content
              with
              | None ->
                  if String.ends_with ~suffix:("\n" ^ end_line) content
                  then Some ()
                  else None
              | Some _ -> Some ()
            in begin match res with
            | Some () -> Reduced (Literal (Bool true, Bool))
            | None -> Reduced (Literal (Bool false, Bool))
            end
        | _ -> Stuck)
    | RemoveBlock -> (Product (Primitive String,
                      Product (Primitive String, Primitive String)),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String begin_line, _),
            Pair (Literal (String end_line, _),
              Literal (String content, _), _), _) ->
            let res =
              let* idx_start =
                if String.starts_with ~prefix:(begin_line ^ "\n") content
                then Some 0
                else String.find_first ~sub:("\n" ^ begin_line ^ "\n") content
              in let* idx_end =
                match String.find_first ~sub:("\n" ^ end_line ^ "\n")
                        ~start:idx_start content
                with
                | None ->
                    if String.ends_with ~suffix:("\n" ^ end_line) content
                    then Some (String.length content)
                    else None
                | Some idx -> Some (idx + String.length end_line + 2)
              in let pre =
                String.sub content 0 idx_start
              in let post =
                if idx_end >= String.length content
                then ""
                else 
                  String.sub content idx_end (String.length content - idx_end)
              in if pre <> "" && post <> ""
              then Some (pre ^ "\n" ^ post)
              else Some (pre ^ post)
            in begin match res with
            | None -> Reduced (Literal (String content, String))
            | Some res -> Reduced (Literal (String res, String))
            end
        | _ -> Stuck)
    | ReplaceBlock -> (Product (Primitive String,
                        Product (Primitive String,
                          Product (Primitive String, Primitive String))),
        Primitive String,
        fun v -> match v with
        | Pair (Literal (String begin_line, _),
            Pair (Literal (String end_line, _),
              Pair (Literal (String content, _),
                Literal (String replacement, _), _), _), _) ->
            let res =
              let* idx_start =
                if String.starts_with ~prefix:(begin_line ^ "\n") content
                then Some 0
                else String.find_first ~sub:("\n" ^ begin_line ^ "\n") content
              in let* idx_end =
                match String.find_first ~sub:("\n" ^ end_line ^ "\n")
                        ~start:idx_start content
                with
                | None ->
                    if String.ends_with ~suffix:("\n" ^ end_line) content
                    then Some (String.length content)
                    else None
                | Some idx -> Some (idx + String.length end_line + 2)
              in let pre =
                if idx_start = 0
                then ""
                else String.sub content 0 idx_start ^ "\n"
              in let post =
                if idx_end >= String.length content
                then ""
                else "\n" ^
                  String.sub content idx_end (String.length content - idx_end)
              in Some (pre ^ replacement ^ post)
            in begin match res with
            | None -> Reduced (Literal (String content, String))
            | Some res -> Reduced (Literal (String res, String))
            end
        | _ -> Stuck)
    | CanBecome -> (Product (Primitive String, Primitive String),
        Primitive Bool,
        fun v -> match v with
        | Pair (Literal (String "root", _), _, _) ->
            Reduced (Literal (Bool true, Bool))
        | Pair (Literal (String init, _), Literal (String become, _), _) ->
            if init = become then Reduced (Literal (Bool true, Bool))
            else Stuck
        | _ -> Stuck)
    | HostIncluded -> (Product (Primitive String, Primitive String),
        Primitive Bool,
        fun v -> match v with
        | Pair (_, Literal (String ("all" | "*"), _), _) ->
            Reduced (Literal (Bool true, Bool))
        | _ -> Stuck)
    | GenExcept (tys, e) ->
        (StringMap.find e tys, Primitive (Exc tys),
          fun v -> Reduced (Literal (Except (tys, e, v), Exc tys)))
    | UnpackExcept (tys, e) ->
        let t = StringMap.find e tys
        in (Primitive (Exc tys), Named (Option t),
            fun v ->
              match v with
              | Literal (Except (_, n, v), _) -> 
                  if n = e
                  (* Some v *)
                  then Reduced (Constructor (Option t, false, v))
                  (* None *)
                  else Reduced (Constructor (Option t, true,
                        Literal (Unit (), Unit)))
              | _ -> Err "Cannot unpack a value that's not an exception")
    | SetAdd ->
        (Product (Primitive String, Primitive StringSet),
         Primitive StringSet,
         fun v -> match v with
         | Pair (Literal (String s, _), Literal (StringSet set, _), _)
            -> Reduced (Literal (StringSet (StringSet.add s set), StringSet))
         | _ -> Stuck)
    | SetContains ->
        (Product (Primitive String, Primitive StringSet),
         Primitive Bool,
         fun v -> match v with
         | Pair (Literal (String k, _), Literal (StringSet set, _), _)
            -> Reduced (Literal (Bool (StringSet.mem k set), Bool))
         | _ -> Stuck)
    (* Uninterpreted functions never reduce *)
    | Uninterpreted (_, in_typ, out_typ) ->
        (in_typ, out_typ, fun _ -> Stuck)

  let literalTyp : literal -> primTy = function
    | Unit   _ -> Unit
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Float  _ -> Float
    | String _ -> String
    | Path   _ -> Path
    | StringSet _ -> StringSet
    | Except (tys, _, _) -> Exc tys

  let attributeDef (_, typ) : typ = typ

  let elementDef (_, typ) : typ = typ

  let actionDef = function
    | (nm, in_typ, out_typ, def) ->
        match !def with
        | Some def -> ("#input", in_typ, out_typ, def)
        | None -> failwith (Printf.sprintf "Function %s was not compiled" nm)

  let isTruthType (t : typ) : bool =
    match t with
    | Primitive Bool -> true
    | _ -> false

  let asTruth (v : value) : bool option =
    match v with
    | Literal (Bool b, Bool) -> Some b
    | _ -> None

  let boolAsValue (b: bool) : value = Literal (Bool b, Bool)

  let equality_func (t : typ) : funct = Equal t

  let isUnit (t : typ) : bool =
    match t with
    | Primitive Unit -> true
    | _ -> false
  let valUnit : value = Literal (Unit (), Unit)
  let listType (t : typ) : namedTy = List t

  type constr = IsBool of bool | IsConstructor of bool * value | IsEqual of value
  type result_constraint = IsBool        of value * bool
                         | IsConstructor of value * (bool * value)
                         | IsEqual       of value * value
  type func_constraints = Unreducible | Reducible of result_constraint list list

  (* Reductions of constraints can leave out any reductions that are handled by
   * the actual definitions, like proj1(pair(x, y)), that will already have
   * simplified by this point and so if we get proj1(x) at this point that means
   * we can't do anything *)
  let reduceFuncConstraint (f: funct) (v: value) (c: constr) =
    match f, c with
    | BoolNeg, IsBool b -> Reducible [[ IsBool (v, not b) ]]
    | BoolOr, IsBool b ->
        begin match v with
        | Pair (x, y, _) ->
            if b
            then Reducible [ [ IsBool (x, true) ]; [ IsBool (y, true) ] ]
            else Reducible [[ IsBool (x, false); IsBool (y, false) ]]
        | _ -> Unreducible
        end
    | BoolAnd, IsBool b ->
        begin match v with
        | Pair (x, y, _) ->
            if b
            then Reducible [[ IsBool (x, true); IsBool (y, true) ]]
            else Reducible [ [ IsBool (x, false) ]; [ IsBool (y, false) ] ]
        | _ -> Unreducible
        end
    | Equal _, IsBool true ->
        begin match v with
        | Pair (x, y, _) -> Reducible [[ IsEqual (x, y) ]]
        | _ -> Unreducible
        end
    (* TODO: Support some reductions involving Concat, ConcatLine, ConsPath,
     * and AddExt (where possible) at least when constrained to be given
     * literals *)
    | ConcatLine, IsEqual r ->
        begin match v, r with
        | Pair (x, o, _), y when x = y ->
            Reducible [[ IsEqual (o, Literal (String "", String)) ]]
        | Pair (o, x, _), y when x = y ->
            Reducible [[ IsEqual (o, Literal (String "", String)) ]]
        | Pair (x, y, _), Literal (String s, _)
          when not (String.contains s '\n') ->
            Reducible [
              [ IsEqual (x, Literal (String "", String))
              ; IsEqual (y, Literal (String s, String)) ];
              [ IsEqual (y, Literal (String "", String))
              ; IsEqual (x, Literal (String s, String)) ] ]
        | Pair (x, y, _), Function (ConcatLine, Pair (vx, vy, _), _) ->
            begin match x, vx, y, vy with
            | Literal (String x, _), Literal (String vx, _), _, _
              when not (String.contains x '\n' || String.contains vx '\n')
                -> if x = vx
                   then Reducible [[ IsEqual (y, vy) ]]
                   else Reducible []
            | _, _, Literal (String y, _), Literal (String vy, _)
              when not (String.contains y '\n' || String.contains vy '\n')
                -> if y = vy
                   then Reducible [[ IsEqual (x, vx) ]]
                   else Reducible []
            | _, _, _, _ ->
                if x = vx 
                then Reducible [[ IsEqual (y, vy) ]]
                else if y = vy
                then Reducible [[ IsEqual (x, vx) ]]
                else Unreducible
            end
        | Pair (x, y, _),
          Function (ReplaceLastMatching,
            Pair (_, Pair (Literal (String rep, _), orig, _), _), _)
            when not (String.contains rep '\n') ->
          (* concat_line(X, Y) <> replace_last_matching(R, W, X) since the left
           * contains all of X and something new at the end while the right
           * contains part of X with W replaced (this holds as long as W does
           * not contain a new line since then we can prove the number of lines
           * will not match)
           * Similarly for concat_line(Y, X) *)
          if x = orig || y = orig
          then Reducible []
          else Unreducible
        | Pair (x, _, _),
          Function (ReplaceBlock,
            Pair (_, Pair (_, Pair (orig, _, _), _), _), _) ->
          (* concat_line(X, Y) <> ReplaceBlock(B, E, X, Z) because the
           * right-hand side never adds anything to the end it only updates X.
           * Technically maybe there's some wild cases where the contents of
           * the block include markers and Y is an end marker, but that's
           * unreasonable in my view. *)
          if x = orig
          then Reducible []
          else Unreducible
        | _, _ -> Unreducible
        end
    | ReplaceLastMatching,
      IsEqual (Function (ReplaceLastMatching,
              Pair (Literal (String regex, _), Pair (repr, orig, _), _), _)) ->
      begin match v with
      | Pair (Literal (String re, _), Pair (w, s, _), _) ->
          if w <> repr || s <> orig
          then Unreducible
          else if re = regex || (re ^ ".*") = regex || (re ^ ".*^") = regex
               || re = (regex ^ ".*") || re = (regex ^ ".*^")
          then Reducible [[]]
          else Unreducible
      | _ -> Unreducible
      end
    | ReplaceLastMatching, IsEqual (Literal (String s, _)) ->
        (* If replace_last_matching(regex, repr, str) is equal to a single
         * line, then that line needs to be equal to repr or str *)
        if not (String.contains s '\n')
        then
          match v with
          | Pair (_, Pair (repr, orig, _), _) ->
              Reducible [ [IsEqual (repr, Literal (String s, String))]
                        ; [IsEqual (orig, Literal (String s, String))] ]
          | _ -> Unreducible
        else Unreducible
    | ReplaceLastMatching, 
      IsEqual (Function (ConcatLine, Pair (x, Literal (String y, _), _), _)) ->
      (* if replace_last_matching(regex, repr, s) = concat_line(x, y)
       * then if y matches regex it must be equal to repr
       * and x = remove_last_line(s) *)
      if not (String.contains y '\n')
      then
        match v with
        | Pair (Literal (String regex, _), Pair (repr, orig, _), _) ->
            begin match compile_regex regex with
            | None -> Unreducible
            | Some regex ->
                if Re.execp regex y
                then Reducible [[ IsEqual (repr, Literal (String y, String));
                    IsEqual (x, 
                      Function (RemoveLastLine, orig, Primitive String)) ]]
                else Unreducible
            end
        | _ -> Unreducible
      else Unreducible
    | ConsPath, IsEqual (Literal (Path p, _)) ->
      begin match v with
      | Pair (Literal (Path x, _), y, _) ->
          let lenx = String.length x
          in let lenp = String.length p
          in if lenx = lenp
          then
            if x = p
            then Reducible [[IsEqual (y, Literal (Path "", Path))]]
            else Reducible []
          else if lenx < lenp
          then
            if String.starts_with ~prefix:x p
            then
              let rem = String.sub p lenx (lenp - lenx)
              in Reducible [[IsEqual (y, Literal (Path rem, Path))]]
            else Reducible []
          else (* lenp < lenx : false because x ^ z <> p if len(x) < len(p) *)
            Reducible []
      | _ -> Unreducible
      end
    | ConsPath, IsEqual (Function (ConsPath, Pair (x, y, t), _)) ->
      begin match v, x with
      | Pair (Literal (Path p, _), q, _), Literal (Path x, _) ->
          let lenp = String.length p
          in let lenx = String.length x
          in if lenp = lenx
          then
            if p = x
            then Reducible [[IsEqual (q, y)]]
            else Reducible []
          else if lenp < lenx
          then
            if String.starts_with ~prefix:p x
            then
              let rem = String.sub x lenp (lenx - lenp)
              in let remval : value = Literal (Path rem, Path)
              in let right : value =
                Function (ConsPath, Pair (remval, y, t), Primitive Path)
              in Reducible [[IsEqual (q, right)]]
            else Reducible []
          else (* lenx < lenp *)
            if String.starts_with ~prefix:x p
            then
              let rem = String.sub p lenx (lenp - lenx)
              in let remval : value = Literal (Path rem, Path)
              in let left : value =
                Function (ConsPath, Pair (remval, q, t), Primitive Path)
              in Reducible [[IsEqual (left, y)]]
            else Reducible []
      | _ -> Unreducible
      end
    | PathFrom, IsEqual (Literal (Path "", _)) ->
      begin match v with
      | Pair (x, y, _) -> Reducible [[IsEqual (x, y)]]
      | _ -> Unreducible
      end
    | PathFrom, IsEqual x ->
      begin match v with
      | Pair (v, w, _) when x = w ->
          Reducible [[IsEqual (v, Literal (Path "", Path))]]
      | _ -> Unreducible
      end
    | BaseName, IsEqual (Literal (Path "", _)) ->
        Reducible [[IsEqual (v, Literal (Path "", Path))]]
    | BaseName, IsEqual (Literal (Path p, _)) ->
        if String.starts_with ~prefix:"/" p
        then Reducible [[IsEqual (v, Literal (Path "/", Path))]]
        else Unreducible
    | EndsWithDir, IsBool b ->
      begin match v with
      | Function (ConsPath, Pair (_, p, _), _) ->
          Reducible [[IsBool (Function (EndsWithDir, p, Primitive Bool), b)]]
      | Function (PathFrom, Pair (_, p, _), _) ->
          Reducible [[IsBool (Function (EndsWithDir, p, Primitive Bool), b)]]
      | _ -> Unreducible
      end
    | _, _ -> Unreducible
end

module TargetInterp = Calculus.Interp.Interp(Ast_Target)

(* Display utilities *)
let rec string_of_type (t : Ast_Target.typ) : string =
  match t with
  | Product (x, y)   -> Printf.sprintf "(%s, %s)" (string_of_type x) (string_of_type y)
  | Primitive Unit   -> "()"
  | Primitive Bool   -> "bool"
  | Primitive Int    -> "int"
  | Primitive Float  -> "float"
  | Primitive String -> "string"
  | Primitive Path   -> "path"
  | Primitive StringSet -> "sset"
  | Primitive (Exc _) -> "exc"
  | Struct tys       ->
      Printf.sprintf "{ %s }"
        (String.concat ", "
          (List.map (fun (nm, t) -> nm ^ ": " ^ string_of_type t)
            (StringMap.to_list tys)))
  | Named (List t)   -> Printf.sprintf "list<%s>" (string_of_type t)
  | Named (Option t) -> Printf.sprintf "option<%s>" (string_of_type t)
  | Named (Cases (nm, _)) -> nm

let rec string_of_value (v : Ast_Target.value) : string =
  match v with
  | Unknown (Loop x, _)         -> "?loop(" ^ string_of_int x ^ ")"
  | Unknown (Universal x, _)    -> "∀" ^ string_of_int x
  | Unknown (Existential x, _)  -> "∃" ^ string_of_int x
  | Literal (Unit (), _)        -> "()"
  | Literal (Bool b, _)         -> string_of_bool b
  | Literal (Int i, _)          -> string_of_int i
  | Literal (Float f, _)        -> string_of_float f
  | Literal (String s, _)       -> "\"" ^ s ^ "\""
  | Literal (Path p, _)         -> "'" ^ p ^ "'"
  | Literal (StringSet s, _) -> "{" ^ String.concat ", " (StringSet.elements s) ^ "}"
  | Literal (Except (_, e, v), _) -> e ^ "(" ^ string_of_value v ^ ")"
  | Pair    (x, y, _)     ->
      "(" ^ string_of_value x ^ ", " ^ string_of_value y ^ ")"
  | Constructor (ty, left, v) ->
      begin match ty with
      | List t ->
          if left
          then Printf.sprintf "nil::<%s>()" (string_of_type t)
          else Printf.sprintf "list::<%s>[%s]" (string_of_type t) (string_of_list_val v)
      | Option t ->
          if left
          then Printf.sprintf "None::<%s>()" (string_of_type t)
          else Printf.sprintf "Some::<%s>(%s)" (string_of_type t) (string_of_value v)
      | Cases (enum, constrs) ->
          string_of_constructor enum constrs left v
      end
  | Struct (_, r) ->
      "{" ^ String.concat ", "
              (List.map (fun (nm, v) -> nm ^ ": " ^ string_of_value v)
                (Ast_Target.FieldMap.to_list r))
          ^ "}"
  | ListVal (_, v) -> "list { " ^ string_of_value v ^ " }"
  | Function (f, arg, _)  ->
      match f with
      | Proj (true, _, _)         -> "proj1(" ^ string_of_value arg ^ ")"
      | Proj (false, _, _)        -> "proj2(" ^ string_of_value arg ^ ")"
      | BoolNeg                   -> "not(" ^ string_of_value arg ^ ")"
      | BoolOr                    -> "or(" ^ string_of_value arg ^ ")"
      | BoolAnd                   -> "and(" ^ string_of_value arg ^ ")"
      | Concat                    -> "concat(" ^ string_of_value arg ^ ")"
      | ConcatLine                -> "concat_line(" ^ string_of_value arg ^ ")"
      | ContainsLine              -> "contains_line(" ^ string_of_value arg ^ ")"
      | RemoveLastLine            -> "remove_line(" ^ string_of_value arg ^ ")"
      | Equal _                   -> "equal(" ^ string_of_value arg ^ ")"
      | Append _                  -> "append(" ^ string_of_value arg ^ ")"
      | ListLength _              -> "len(" ^ string_of_value arg ^ ")"
      | AddInt                    -> "add(" ^ string_of_value arg ^ ")"
      | AddFloat                  -> "add(" ^ string_of_value arg ^ ")"
      | SubInt                    -> "sub(" ^ string_of_value arg ^ ")"
      | SubFloat                  -> "sub(" ^ string_of_value arg ^ ")"
      | MulInt                    -> "mul(" ^ string_of_value arg ^ ")"
      | MulFloat                  -> "mul(" ^ string_of_value arg ^ ")"
      | DivInt                    -> "div(" ^ string_of_value arg ^ ")"
      | DivFloat                  -> "div(" ^ string_of_value arg ^ ")"
      | Modulo                    -> "mod(" ^ string_of_value arg ^ ")"
      | Power                     -> "pow(" ^ string_of_value arg ^ ")"
      | LShift                    -> "lshift(" ^ string_of_value arg ^ ")"
      | RShift                    -> "rshift(" ^ string_of_value arg ^ ")"
      | LtInt                     -> "lt(" ^ string_of_value arg ^ ")"
      | LtFloat                   -> "lt(" ^ string_of_value arg ^ ")"
      | LeInt                     -> "le(" ^ string_of_value arg ^ ")"
      | LeFloat                   -> "le(" ^ string_of_value arg ^ ")"
      | ToLower                   -> "to_lower(" ^ string_of_value arg ^ ")"
      | Substring                 -> "substring(" ^ string_of_value arg ^ ")"
      | StringSubst               -> "string_subst(" ^ string_of_value arg ^ ")"
      | StringOfInt               -> "string_of_int(" ^ string_of_value arg ^ ")"
      | StringOfFloat             -> "string_of_float(" ^ string_of_value arg ^ ")"
      | StringOfBool              -> "string_of_bool(" ^ string_of_value arg ^ ")"
      | FloatOfInt                -> "float_of_int(" ^ string_of_value arg ^ ")"
      | ConsPath                  -> "cons_path(" ^ string_of_value arg ^ ")"
      | PathOfString              -> "path_of_string(" ^ string_of_value arg ^ ")"
      | StringOfPath              -> "string_of_path(" ^ string_of_value arg ^ ")"
      | EndsWithDir               -> "ends_with_dir(" ^ string_of_value arg ^ ")"
      | BaseName                  -> "base_name(" ^ string_of_value arg ^ ")"
      | PathFrom                  -> "path_from(" ^ string_of_value arg ^ ")"
      | AddExt                    -> "add_ext(" ^ string_of_value arg ^ ")"
      | NormalizePath             -> "norm_path(" ^ string_of_value arg ^ ")"
      | RegexOfLiteral            -> "regex_of_literal(" ^ string_of_value arg ^ ")"
      | RemoveMatchingLines       -> "remove_matching_lines(" ^ string_of_value arg ^ ")"
      | ReplaceLastMatchingExpand -> "replace_last_matching_expand(" ^ string_of_value arg ^ ")"
      | ReplaceLastMatching       -> "replace_last_matching(" ^ string_of_value arg ^ ")"
      | InsertNearMatching        -> "insert_line_matching(" ^ string_of_value arg ^ ")"
      | RegexLineMatches          -> "line_matches_regex(" ^ string_of_value arg ^ ")"
      | GetLastLineMatch          -> "last_line_matching(" ^ string_of_value arg ^ ")"
      | FindBlock                 -> "find_block(" ^ string_of_value arg ^ ")"
      | RemoveBlock               -> "remove_block(" ^ string_of_value arg ^")"
      | ReplaceBlock              -> "replace_block(" ^ string_of_value arg ^")"
      | CanBecome                 -> "can_become(" ^ string_of_value arg ^ ")"
      | HostIncluded              -> "host_included(" ^ string_of_value arg ^ ")"
      | Uninterpreted (nm, _, _)  -> nm ^ "(" ^ string_of_value arg ^ ")"
      | EmptyStruct _             -> "{ }"
      | AddField (_, f)           -> "set." ^ f ^ "(" ^ string_of_value arg ^ ")"
      | ReadField (_, f)          -> "get." ^ f ^ "(" ^ string_of_value arg ^ ")"
      | GenUniversal _            -> "?∀"
      | GenExistential _          -> "?∃"
      | Constructor (w, _)        ->
          (if w then "L" else "R") ^ "(" ^ string_of_value arg ^ ")"
      | GenExcept (_, e)          -> "except_" ^ e ^ "(" ^ string_of_value arg ^ ")"
      | UnpackExcept (_, e)       -> "unpack_" ^ e ^ "(" ^ string_of_value arg ^ ")"
      | SetAdd                    -> "set_add(" ^ string_of_value arg ^ ")"
      | SetContains               -> "set_contains(" ^ string_of_value arg ^ ")"
and string_of_list_val (v : Ast_Target.value) : string =
  match v with
  | Pair (hd, tl, _) ->
      string_of_value hd
      ^ begin match tl with
        | Constructor (_, is_nil, lst) ->
            if is_nil then "" else "; " ^ string_of_list_val lst
        | Unknown (_, _) -> ";" ^ string_of_value v ^ " ..."
        | _ -> "; <<ERROR: MALFORMED LIST>>"
        end
  | Unknown (_, _) -> string_of_value v ^ " ..."
  | _ -> "<<ERROR: MALFORMED LIST>>"
and string_of_constructor enum constr is_first v =
  match constr, is_first with
  | LastTwo ((nm, _), _), true
  | Cons    ((nm, _), _), true
    -> enum ^ "::" ^ nm ^ "(" ^ string_of_value v ^ ")"
  | LastTwo (_, (nm, _)), false
    -> enum ^ "::" ^ nm ^ "(" ^ string_of_value v ^ ")"
  | Cons (_, cs), false
    -> match v with
       | Constructor (_, is_first, v) -> string_of_constructor enum cs is_first v
       | Unknown (_, _) -> string_of_value v
       | _ -> "<< ERROR: MALFORMED ENUM VALUE >>"

let rec string_of_expr (e : Ast_Target.expr) : string =
  match e with
  | Variable v         -> v
  | Literal (Unit ())  -> "()"
  | Literal (Bool b)   -> string_of_bool b
  | Literal (Int i)    -> string_of_int i
  | Literal (Float f)  -> string_of_float f
  | Literal (String s) -> "\"" ^ s ^ "\""
  | Literal (Path p)   -> "'" ^ p ^ "'"
  | Literal (StringSet s) -> "{" ^ String.concat ", " (StringSet.elements s) ^ "}"
  | Literal (Except (_, e, v)) -> e ^ "(" ^ string_of_value v ^ ")"
  | Pair (x, y)        ->
      "(" ^ string_of_expr x ^ ", " ^ string_of_expr y ^ ")"
  | Function (f, e) ->
      let string_f =
        match f with
        | Proj (true, _, _)         -> "proj1"
        | Proj (false, _, _)        -> "proj2"
        | Constructor (true, _)     -> "L"
        | Constructor (false, _)    -> "R"
        | EmptyStruct _             -> "{}"
        | AddField (_, field)       -> "add#" ^ field
        | ReadField (_, field)      -> "get#" ^ field
        | GenUniversal _            -> "?∀"
        | GenExistential _          -> "?∃"
        | BoolNeg                   -> "not"
        | BoolOr                    -> "or"
        | BoolAnd                   -> "and"
        | Concat                    -> "concat"
        | ConcatLine                -> "concat_line"
        | ContainsLine              -> "contains_line"
        | RemoveLastLine            -> "remove_line"
        | Equal _                   -> "equal"
        | Append _                  -> "append"
        | ListLength _              -> "len"
        | AddInt                    -> "add"
        | AddFloat                  -> "add"
        | SubInt                    -> "sub"
        | SubFloat                  -> "sub"
        | MulInt                    -> "mul"
        | MulFloat                  -> "mul"
        | DivInt                    -> "div"
        | DivFloat                  -> "div"
        | Modulo                    -> "mod"
        | Power                     -> "pow"
        | LShift                    -> "lshift"
        | RShift                    -> "rshift"
        | LtInt                     -> "lt"
        | LtFloat                   -> "lt"
        | LeInt                     -> "le"
        | LeFloat                   -> "le"
        | ToLower                   -> "to_lower"
        | Substring                 -> "substring"
        | StringSubst               -> "string_subst"
        | StringOfInt               -> "string_of_int"
        | StringOfFloat             -> "string_of_float"
        | StringOfBool              -> "string_of_bool"
        | FloatOfInt                -> "float_of_int"
        | ConsPath                  -> "cons_path"
        | PathOfString              -> "path_of_string"
        | StringOfPath              -> "string_of_path"
        | EndsWithDir               -> "ends_with_dir"
        | BaseName                  -> "base_name"
        | PathFrom                  -> "path_from"
        | AddExt                    -> "add_ext"
        | NormalizePath             -> "norm_path"
        | RegexOfLiteral            -> "regex_of_literal"
        | RemoveMatchingLines       -> "remove_matching_lines"
        | ReplaceLastMatchingExpand -> "replace_last_matching_expand"
        | ReplaceLastMatching       -> "replace_last_matching"
        | InsertNearMatching        -> "insert_line_matching"
        | RegexLineMatches          -> "line_matches_regex"
        | GetLastLineMatch          -> "last_line_matching"
        | FindBlock                 -> "find_block"
        | RemoveBlock               -> "remove_block"
        | ReplaceBlock              -> "replace_block"
        | CanBecome                 -> "can_become"
        | HostIncluded              -> "host_included"
        | GenExcept (_, e)          -> "except_" ^ e
        | UnpackExcept (_, e)       -> "unpack_" ^ e
        | SetAdd                    -> "set_add"
        | SetContains               -> "set_contains"
        | Uninterpreted (nm, _, _)  -> nm
      in string_f ^ "(" ^ string_of_expr e ^ ")"

let rec string_of_qual (q : Ast_Target.qual) : string =
  match q with
  | Attribute ((attr, _), e) ->
      attr ^ " = " ^ string_of_expr e
  | Element ((elem, _), e, q) ->
      elem ^ "(" ^ string_of_expr e ^ ")"
      ^ (match q with
        | None -> ""
        | Some q -> " : < " ^ string_of_qual q ^ " >")
  | NotElement ((elem, _), e) ->
      "!" ^ elem ^ "(" ^ string_of_expr e ^ ")"

let rec string_of_attr (a : Ast_Target.attr) : string =
  match a with
  | AttrAccess ((attr, _)) -> attr
  | OnElement ((elem, _), e, rest) ->
      elem ^ "(" ^ string_of_expr e ^ ")." ^ string_of_attr rest

let rec string_of_elem (e : Ast_Target.elem) : string =
  match e with
  | Element ((elem, _), e) -> elem ^ "(" ^ string_of_expr e ^ ")"
  | OnElement ((elem, _), e, rest) ->
      elem ^ "(" ^ string_of_expr e ^ ")." ^ string_of_elem rest

let string_of_stmt (s : Ast_Target.stmt) : string =
  let rec process (s : Ast_Target.stmt) (indent : string) : string =
    match s with
    | Seq (fst, snd) ->
        process fst indent ^ "\n" ^ process snd indent
    | Action (v, (nm, _, _, _), arg) ->
        indent ^ v ^ " = " ^ nm ^ "{" ^ string_of_expr arg ^ "}"
    | Assign (v, e) ->
        indent ^ v ^ " = " ^ string_of_expr e
    | Add (q) ->
        indent ^ "add " ^ string_of_qual q
    | Get (v, a) ->
        indent ^ v ^ " = get " ^ string_of_attr a
    | Contains (q, th, el) ->
        indent ^ "contains " ^ string_of_elem q ^ " {\n"
        ^ process th ("\t" ^ indent) ^ "\n"
        ^ indent ^ "} else {\n"
        ^ process el ("\t" ^ indent) ^ "\n"
        ^ indent ^ "}"
    | Cond (e, th, el) ->
        indent ^ "if " ^ string_of_expr e ^ "{\n"
        ^ process th ("\t" ^ indent) ^ "\n"
        ^ indent ^ "} else {\n"
        ^ process el ("\t" ^ indent) ^ "\n"
        ^ indent ^ "}"
    | Match (e, v, l, r) ->
        indent ^ "match " ^ string_of_expr e ^ " with {\n"
        ^ indent ^ "\tL(" ^ v ^ ") => {\n"
        ^ process l ("\t\t" ^ indent) ^ "\n"
        ^ indent ^ "\t}\n"
        ^ indent ^ "\tR(" ^ v ^ ") => {\n"
        ^ process r ("\t\t" ^ indent) ^ "\n"
        ^ indent ^ "\t}\n"
        ^ indent ^ "}"
    | ForEach (v, _, lst, w, body) ->
        indent ^ v ^ " = foreach " ^ w ^ " in " ^ string_of_expr lst ^ " {\n"
        ^ process body ("\t" ^ indent) ^ "\n"
        ^ indent ^ "}"
    | TryCatch (body, evar, catch, finally) ->
        indent ^ "try {\n"
        ^ process body ("\t" ^ indent) ^ "\n"
        ^ indent ^ "} catch " ^ evar ^ "{\n"
        ^ process catch ("\t" ^ indent) ^ "\n"
        ^ indent ^ "} finally {\n"
        ^ process finally ("\t" ^ indent) ^ "\n"
        ^ indent ^ "}"
    | Localize ((elem, _), ex, body) ->
        indent ^ "localize " ^ elem ^ "(" ^ string_of_expr ex ^ ") {\n"
        ^ process body ("\t" ^ indent) ^ "\n"
        ^ indent ^ "}"
    | Raise e ->
        indent ^ "raise " ^ string_of_expr e
    | Return e ->
        indent ^ "return " ^ string_of_expr e
    | Yield e ->
        indent ^ "yield " ^ string_of_expr e
    | Pass ->
        indent ^ "pass"
  in process s ""

let string_of_list empty lhs sep rhs f lst : string =
  if List.is_empty lst
  then empty
  else lhs ^ String.concat sep (List.map f lst) ^ rhs

let string_of_state (state : TargetInterp.state) : string =
  let rec inner_string_of_state if_empty lhs rhs (state : TargetInterp.state) =
    let State(elems, attrs) = state
    in string_of_list if_empty lhs ", " rhs (fun s -> s)
        (List.map
          (fun (((elem, _), v), (s : TargetInterp.element_result)) ->
            match s with
            | Negated -> "not " ^ elem ^ "(" ^ string_of_value v ^ ")"
            | Positive s ->
                elem ^ "(" ^ string_of_value v ^ ")"
                ^ inner_string_of_state "" ": <" " >" s)
          (TargetInterp.ElementMap.to_list elems)
        @
        List.map
          (fun ((attr, _), v) -> attr ^ " = " ^ string_of_value v)
          (TargetInterp.AttributeMap.to_list attrs))
  in inner_string_of_state "<>" "< " " >" state

let string_of_constructor_constraint (v: Ast_Target.value) (left: bool)
  (arg: Ast_Target.value) : string =
  let ty : Ast_Target.typ = TargetInterp.type_of_val v
  in string_of_value v ^ " = " ^
  match ty with
  | Named ty ->
      begin match ty with
      | List t ->
          if left
          then Printf.sprintf "nil::<%s>()" (string_of_type t)
          else Printf.sprintf "list::<%s>[%s]" (string_of_type t) (string_of_list_val arg)
      | Option t ->
          if left
          then Printf.sprintf "None::<%s>()" (string_of_type t)
          else Printf.sprintf "Some::<%s>(%s)" (string_of_type t) (string_of_value arg)
      | Cases (enum, constrs) ->
          string_of_constructor enum constrs left arg
      end
  | _ -> "<< ERROR: MALFORMED CONSTRUCTOR CONSTRAINT >>"

let string_of_loop_info (i: TargetInterp.loop_info) : string =
  match i with
  | AllUnknown i -> "#" ^ string_of_int i
  | AllKnown v -> string_of_value v
  | LastKnown (i, v) -> "#" ^ string_of_int i ^ "/" ^ string_of_value v

let string_of_interp_state (state : TargetInterp.interp_state) : string =
  Printf.sprintf "%s --> %s [{ %s }, { %s }, { %s }]"
    (string_of_state state.init)
    (string_of_state state.final)
    (String.concat ", "
      (List.map (fun (v, i) -> string_of_value v ^ ": " ^ string_of_loop_info i)
        (TargetInterp.ValueMap.to_list state.loops)))
    (String.concat ", "
      (List.map (fun (v, b) -> string_of_value v ^ " = " ^ string_of_bool b)
        (TargetInterp.ValueMap.to_list state.bools)))
    (String.concat ", "
      (List.map (fun (v, (b, w)) -> string_of_constructor_constraint v b w)
        (TargetInterp.ValueMap.to_list state.constrs)))

let string_of_res (res : TargetInterp.interp_res) : (string, string) result =
  let rec string_of_res (res : TargetInterp.interp_res) (indent : int)
    (is_all : bool) : (string, string) result =
    let prefix =
      String.make indent '\t'
      ^ match indent mod 3 with
      | 0 -> "- "
      | 1 -> "+ "
      | _ -> "* "
    in match res with
    | Err msg -> Error msg
    | Success s -> Ok (prefix ^ string_of_interp_state s)
    | Both (x, y) ->
        let new_indent = if is_all then indent else indent + 1
        in begin match
          string_of_res x new_indent true, string_of_res y new_indent true
        with
        | Ok x, Ok y ->
            if is_all
            then Ok (x ^ "\n" ^ y)
            else Ok (prefix ^ "ALL\n" ^ x ^ "\n" ^ y)
        | Error _, Ok r | Ok r, Error _ ->
            if is_all
            then Ok r
            else Ok (prefix ^ "ALL\n" ^ r)
        | Error x, Error y -> Error (x ^ "\n" ^ y)
        end
    | Either (x, y) ->
        let new_indent = if is_all then indent + 1 else indent
        in begin match
          string_of_res x new_indent false, string_of_res y new_indent false
        with
        | Ok x, Ok y ->
            if is_all
            then Ok (prefix ^ "SOME\n" ^ x ^ "\n" ^ y)
            else Ok (x ^ "\n" ^ y)
        | Error _, Ok r | Ok r, Error _ ->
            if is_all
            then Ok (prefix ^ "SOME\n" ^ r)
            else Ok r
        | Error x, Error y -> Error (x ^ "\n" ^ y)
        end
  in match res with
  | Err msg -> Error msg
  | Success s -> Ok (string_of_interp_state s)
  | Both (x, y) ->
      begin match string_of_res x 0 true, string_of_res y 0 true with
      | Ok x, Ok y -> Ok ("ALL\n" ^ x ^ "\n" ^ y)
      | Error _, Ok r | Ok r, Error _ -> Ok ("ALL\n" ^ r)
      | Error x, Error y -> Error (x ^ "\n" ^ y)
      end
  | Either (x, y) ->
      begin match string_of_res x 0 false, string_of_res y 0 false with
      | Ok x, Ok y -> Ok ("SOME\n" ^ x ^ "\n" ^ y)
      | Error _, Ok r | Ok r, Error _ -> Ok ("SOME\n" ^ r)
      | Error x, Error y -> Error (x ^ "\n" ^ y)
      end
