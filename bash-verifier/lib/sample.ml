open Calculus.Ast
open Calculus.Builtin
open Calculus.Interp
open Calculus.Value

module Builtin = struct
  type lit = Unit
           | Bool   of bool
           | Int    of int
           | Float  of float
           | String of string
           | Path   of string

  type func = Add
            | Sub
            | Mul
            | Div
            | Modulo
            | Lt
            | Le
            | Gt
            | Ge
            | Eq
            | ConcatStr
            | SplitPath

  type act = |
end

module Defs = struct
  type func = Builtin.func
  type act  = Builtin.act

  module V = Value(Builtin)
  type v = V.t

  module C = Ast(Builtin)
  type stmt = C.stmt

  open V

  let as_bool = function
    | Literal (Bool b) -> Some b
    | _                -> None

  let rec as_list = function
    | Left (Literal Unit) -> Some []
    | Right (Pair (hd, tl)) -> Option.map (fun tl -> hd :: tl) (as_list tl)
    | _ -> None

  let rec of_list = function
    | [] -> Left (Literal Unit)
    | hd :: tl -> Right (Pair (hd, of_list tl))

  let mixed_numeric (ki : int -> int -> int) (kf : float -> float -> float)
  = function
    | Pair (Literal (Int x),   Literal (Int y))   ->
        Some (Literal (Int (ki x y)))
    | Pair (Literal (Int x),   Literal (Float y)) ->
        Some (Literal (Float (kf (float_of_int x) y)))
    | Pair (Literal (Float x), Literal (Int y))   ->
        Some (Literal (Float (kf x (float_of_int y))))
    | Pair (Literal (Float x), Literal (Float y)) ->
        Some (Literal (Float (kf x y)))
    | _ -> None

  let mixed_numeric_bool
    (ki : int -> int -> bool) (kf : float -> float -> bool)
  = function
    | Pair (Literal (Int x),   Literal (Int y))   ->
        Some (Literal (Bool (ki x y)))
    | Pair (Literal (Int x),   Literal (Float y)) ->
        Some (Literal (Bool (kf (float_of_int x) y)))
    | Pair (Literal (Float x), Literal (Int y))   ->
        Some (Literal (Bool (kf x (float_of_int y))))
    | Pair (Literal (Float x), Literal (Float y)) ->
        Some (Literal (Bool (kf x y)))
    | _ -> None

  let ints (k : int -> int -> int) = function
    | Pair (Literal (Int x), Literal (Int y)) -> Some (Literal (Int (k x y)))
    | _ -> None

  let strings (k : string -> string -> string) = function
    | Pair (Literal (String x), Literal (String y)) ->
        Some (Literal (String (k x y)))
    | _ -> None

  let pair_uncurry (k : v -> v -> v option) = function
    | Pair (x, y) -> k x y
    | _ -> None

  let values_equal x y : v option =
    let rec equal x y : bool =
      match x, y with
      | Literal x, Literal y -> x = y
      | Pair (x1, x2), Pair (y1, y2) -> equal x1 y1 && equal x2 y2
      | Left x, Left y -> equal x y
      | Right x, Right y -> equal x y
      | Struct xs, Struct ys -> V.FieldMap.equal equal xs ys
      | SRef x, SRef y -> x = y
      | _, _ -> false
    in Some (Literal (Bool (equal x y)))

  let split_path = function
    | Literal (Path p) -> 
        Some (of_list (List.map (fun s -> Literal (Path s))
          (String.split_all ~sep:"/" ~drop:String.is_empty p)))
    | _ -> None

  let func_def (f : Builtin.func) : v -> v option =
    match f with
    | Add       -> mixed_numeric ( + ) ( +. )
    | Sub       -> mixed_numeric ( - ) ( -. )
    | Mul       -> mixed_numeric ( * ) ( *. )
    | Div       -> mixed_numeric ( / ) ( /. )
    | Modulo    -> ints ( mod )
    | Lt        -> mixed_numeric_bool ( <  ) ( <  )
    | Le        -> mixed_numeric_bool ( <= ) ( <= )
    | Gt        -> mixed_numeric_bool ( >  ) ( >  )
    | Ge        -> mixed_numeric_bool ( >= ) ( >= )
    | Eq        -> pair_uncurry values_equal
    | ConcatStr -> strings (^)
    | SplitPath -> split_path

  let act_def : act -> stmt = function _ -> .
end

module SampleConcrete = InterpConcrete(Builtin)(Defs)
module SampleRandomize = InterpRandomize(Builtin)(Defs)
