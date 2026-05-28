open Calculus.Ast

type atts = Content | Count
type elms = Local | File | Dir | Fd
type lits = String of string | Path of string | Bool of bool | Int of int | Unit
type prim = String | Path | Bool | Int | Unit

type 't funcs = Equals of 't | IsZero
type 't named = List of 't

type empty = |

module rec Calc : Ast_Defs
  with type variable  = string
  with type attribute = atts
  with type element   = elms
  with type literal   = lits
  with type primTy    = prim
  with type funct     = Calc.typ funcs
  with type namedTy   = Calc.typ named

  with type structTy  = empty
= struct
  type primTy = prim

  type field  = string
  module FieldMap = Map.Make(String)

  type namedTy  = typ named
   and structTy = empty
   and typ = Product   of typ * typ
           | Primitive of primTy
           | Named     of namedTy
           | Struct    of structTy

  type funct = typ funcs

  type variable = string
  module VariableMap = Map.Make(String)

  type literal = lits
   and record  = value FieldMap.t
   and value   = Unknown     of id * typ
               | Literal     of literal * primTy
               | Function    of funct * value * typ
               | Pair        of value * value * typ
               | Constructor of namedTy * bool * value
               | Struct      of structTy * record
               | ListVal     of namedTy * value

  type attribute = atts
  type element   = elms

  type expr = Function of funct * expr
            | Literal  of literal
            | Variable of variable
            | Pair     of expr * expr

  type qual = Attribute   of attribute * expr
            | Element     of element * expr * qual option
            | NotElement  of element * expr
  type attr = AttrAccess  of attribute
            | OnElement   of element * expr * attr
  type elem = Element     of element * expr
            | OnElement   of element * expr * elem

  type action = |
   and stmt = Seq      of stmt * stmt
            | Action   of variable * action * expr
            | Assign   of variable * expr
            | Add      of qual
            | Get      of variable * attr
            | Contains of elem * stmt * stmt
            | Cond     of expr * stmt * stmt
            | Match    of expr * variable (* value in constructor *)
                        * stmt * stmt (* left and right cases *)
            | ForEach  of variable (* variable for result of for-each *)
                        * typ (* element type of the result *)
                        * expr * variable (* list and element var *)
                        * stmt (* body *)
            | TryCatch of stmt (* body of try *)
                        * variable * stmt (* exception name and handler *)
                        * stmt (* finally body *)
            | Localize of element * expr * stmt
            | Raise    of expr
            | Return   of expr
            | Yield    of expr (* yield for a foreach statement *)
            | Pass

  let namedTyDef : namedTy -> typ * typ = function
    | List t -> (Primitive Unit, Product (t, Named (List t)))

  let structTyDef : structTy -> _ = function _ -> .

  let funcDef = function
    | Equals t -> (Product (t, t), Primitive Bool,
        fun (v : value) : value eval ->
          match v with
          | Pair (x, y, _) -> Reduced (Literal (Bool (x = y), Bool))
          | _ -> Stuck)
    | IsZero -> (Primitive Int, Primitive Bool,
        fun (v : value) : value eval ->
          match v with
          | Literal (Int x, _) -> Reduced (Literal (Bool (x = 0), Bool))
          | _ -> Stuck)

  let literalTyp : literal -> primTy = function
    | String _ -> String
    | Path   _ -> Path
    | Bool   _ -> Bool
    | Int    _ -> Int
    | Unit     -> Unit

  let attributeDef : attribute -> typ = function
    | Content -> Primitive String
    | Count -> Primitive Int

  let elementDef : element -> typ = function
    | File -> Primitive Path
    | Dir  -> Primitive Path
    | Local -> Primitive Unit
    | Fd    -> Primitive Int

  let actionDef : action -> _ = function _ -> .

  let isTruthType (t : typ)   : bool =
    match t with
    | Primitive Bool -> true
    | _ -> false
  let asTruth     (v : value) : bool option =
    match v with
    | Literal (Bool b, _) -> Some b
    | _ -> None
  let boolAsValue (b : bool)  : value = Literal (Bool b, Bool)

  let equality_func (t : typ) : funct = Equals t

  let isUnit      (t : typ)   : bool =
    match t with
    | Primitive Unit -> true
    | _ -> false
  let valUnit : value = Literal (Unit, Unit)
  let listType    (t : typ)   : namedTy = List t

  type constr = IsBool of bool | IsConstructor of bool * value | IsEqual of value
  type result_constraint = IsBool        of value * bool
                         | IsConstructor of value * (bool * value)
                         | IsEqual       of value * value
  type func_constraints = Unreducible | Reducible of result_constraint list list

  let reduceFuncConstraint (f : funct) (v : value) (c : constr)
    : func_constraints =
    match f with
    | Equals _ ->
        begin match c with
        | IsBool true ->
            begin match v with
            | Pair (x, y, _) -> Reducible [[IsEqual (x, y)]]
            | _ -> Unreducible
            end
        | _ -> Unreducible
        end
    | IsZero ->
        begin match c with
        | IsBool true -> Reducible [[IsEqual (v, Literal (Int 0, Int))]]
        | _ -> Unreducible
        end
end

module CalcInterp = Calculus.Interp.Interp(Calc)

let rec string_of_value (v : Calc.value) : string =
  match v with
  | Unknown (Loop x, _)   -> "?loop(" ^ string_of_int x ^ ")"
  | Unknown (Universal x, _)    -> "∀" ^ string_of_int x
  | Unknown (Existential x, _)    -> "∃" ^ string_of_int x
  | Literal (String s, _) -> "\"" ^ s ^ "\""
  | Literal (Path p, _)   -> "'" ^ p ^ "'"
  | Literal (Bool b, _)   -> string_of_bool b
  | Literal (Int i, _)    -> string_of_int i
  | Literal (Unit, _)     -> "()"
  | Pair (x, y, _) -> "(" ^ string_of_value x ^ ", " ^ string_of_value y ^ ")"
  | Struct (_, _) -> .
  | Constructor (List _, _, _) -> "[" ^ string_of_list v ^ "]"
  | Function (Equals _, Pair (x, y, _), _) ->
      string_of_value x ^ " == " ^ string_of_value y
  | Function (Equals _, v, _) -> "==(" ^ string_of_value v ^ ")"
  | Function (IsZero, v, _) -> "isZero(" ^ string_of_value v ^ ")"
  | ListVal (List _, v) -> "list { " ^ string_of_value v ^ " }"
and string_of_list ?(sep = false) (v : Calc.value) : string =
  match v with
  | Constructor (List _, true, _) -> ""
  | Constructor (List _, false, Pair (hd, tl, _)) ->
      (if sep then "; " else "") ^ string_of_value hd
      ^ string_of_list ~sep:true tl
  | _ -> (if sep then "; " else "") ^ "~" ^ string_of_value v

let string_of_element (e : Calc.element) : string =
  match e with
  | File  -> "file"
  | Dir   -> "dir"
  | Local -> "local"
  | Fd    -> "fd"

let string_of_attribute (a : Calc.attribute) : string =
  match a with
  | Content -> "content"
  | Count   -> "count"

let string_of_list empty lhs sep rhs f lst : string =
  if List.is_empty lst
  then empty
  else lhs ^ String.concat sep (List.map f lst) ^ rhs

let string_of_state (state: CalcInterp.state) : string =
  let rec inner_string_of_state empty lhs rhs (state: CalcInterp.state) =
    let State(elems, attrs) = state
    in string_of_list empty lhs ", " rhs (fun s -> s)
      (List.map
        (fun ((elem, v), (s : CalcInterp.element_result)) ->
          match s with
          | Negated -> 
              "not " ^ string_of_element elem ^ "(" ^ string_of_value v ^ ")"
          | Positive s ->
              string_of_element elem ^ "(" ^ string_of_value v ^ ")"
              ^ inner_string_of_state "" ": < " " >" s)
        (CalcInterp.ElementMap.to_list elems)
      @
      List.map
        (fun (attr, v) ->
          string_of_attribute attr ^ " = " ^ string_of_value v)
        (CalcInterp.AttributeMap.to_list attrs))
  in inner_string_of_state "<>" "< " " >" state

let string_of_loop_info (i: CalcInterp.loop_info) : string =
  match i with
  | AllUnknown i -> "#" ^ string_of_int i
  | AllKnown v -> string_of_value v
  | LastKnown (i, v) -> "#" ^ string_of_int i ^ "/" ^ string_of_value v

let string_of_interp_state (s : CalcInterp.interp_state) : string =
  Printf.sprintf "%s --> %s [{ %s }, { %s }, { %s }]"
    (string_of_state s.init)
    (string_of_state s.final)
    (String.concat ", "
      (List.map (fun (v, i) -> string_of_value v ^ ": " ^ string_of_loop_info i)
        (CalcInterp.ValueMap.to_list s.loops)))
    (String.concat ", "
      (List.map (fun (v, b) -> string_of_value v ^ " = " ^ string_of_bool b)
        (CalcInterp.ValueMap.to_list s.bools)))
    (String.concat ", "
      (List.map (fun (v, (b, w)) -> string_of_value v ^ " = "
                  ^ (if b then "L" else "R") ^ "(" ^ string_of_value w ^ ")")
        (CalcInterp.ValueMap.to_list s.constrs)))

let rec string_of_interp_res (res : CalcInterp.interp_res)
  : (string, string) result =
  match res with
  | Err msg -> Error msg
  | Success s -> Ok (string_of_interp_state s)
  | Both (x, y) ->
      begin match string_of_interp_res x, string_of_interp_res y with
      | Ok x, Ok y -> Ok (x ^ "\n" ^ y)
      | Ok r, Error _ | Error _, Ok r -> Ok r
      | Error x, Error y -> Error (x ^ "\n" ^ y)
      end
  | Either (x, y) ->
      begin match string_of_interp_res x, string_of_interp_res y with
      | Ok x, Ok y -> Ok (Printf.sprintf "[\n%s\n\n%s\n]" x y)
      | Ok r, Error _ | Error _, Ok r -> Ok r
      | Error x, Error y -> Error (x ^ "\n" ^ y)
      end

let rec seq (s : Calc.stmt list) : Calc.stmt =
  match s with
  | [] -> Assign ("_", Literal Unit)
  | [s] -> s
  | hd :: tl -> Seq (hd, seq tl)

let example1 : Calc.stmt =
  seq
    [ Get ("c", OnElement (File, Variable "S", AttrAccess Content))
    ; Add (Element (File, Variable "D", Some (Attribute (Content, Variable "c"))))
    ; Add (NotElement (File, Variable "S"))
    ; Return (Literal Unit) ]

let full1 : Calc.stmt =
  seq
    [ Assign ("S", Literal (Path "/path/to/src"))
    ; Assign ("D", Literal (Path "/path/to/dst"))
    ; Contains (Element (File, Variable "S"),
        example1,
        Raise (Literal (String "Missing source file"))) ]

let example2 : Calc.stmt =
  Contains (Element (File, Variable "S"),
    example1,
    Return (Literal Unit))

let full2 : Calc.stmt =
  seq
    [ Assign ("S", Literal (Path "/path/to/src"))
    ; Assign ("D", Literal (Path "/path/to/dst"))
    ; example2 ]

let test1 : Calc.stmt =
  Contains (Element (File, Literal (Path "foo")),
    Seq (
      Add (NotElement (File, Literal (Path "foo"))),
      Get ("x", OnElement (File, Literal (Path "foo"), AttrAccess Content))),
    Raise (Literal (String "file does not exist")))

let test2 : Calc.stmt =
  Contains (OnElement (Dir, Literal (Path "a"),
              OnElement (Dir, Literal (Path "b"),
                Element (File, Literal (Path "c")))),
    Return (Literal Unit),
    Raise (Literal (String "file does not exist")))

let test3 : Calc.stmt =
  Contains (Element (Dir, Literal (Path "a")),
    Raise (Literal (String "file should not exist")),
    Seq (
      Add (Element (Dir, Literal (Path "a"), None)),
      Contains (OnElement (Dir, Literal (Path "a"),
                  Element (File, Literal (Path "b"))),
        Raise (Literal (String "file does not exist")),
        Return (Literal Unit)
      )
    )
  )

let test4 : Calc.stmt =
  Contains (OnElement (Local, Literal Unit, Element (Fd, Literal (Int 0))),
    Seq (
      Get ("v", OnElement (Local, Literal Unit,
                  OnElement (Fd, Literal (Int 0),
                    AttrAccess Count))),
      Cond (
        Function (IsZero, Variable "v"),
        Seq (
          Add (Element (Local, Literal Unit, Some (
                Element (Fd, Literal (Int 1), Some (
                  Attribute (Count, Literal (Int 7))))))),
        Seq (
          Add (Element (Local, Literal Unit, Some (
                Element (Fd, Literal (Int 0), Some (
                  Attribute (Count, Literal (Int 1))))))),
          Localize (Local, Literal Unit,
            Seq (
              Add (Element (Local, Literal Unit, Some (
                    Element (Fd, Literal (Int 0), Some (
                      Attribute (Count, Literal (Int 3))))))),
            Seq (
              Add (Element (Local, Literal Unit, Some (
                    NotElement (Fd, Literal (Int 1))))),
            Seq (
              Get ("v", OnElement (Local, Literal Unit,
                          OnElement (Fd, Literal (Int 2),
                            AttrAccess Count))),
              Add (Element (Local, Literal Unit, Some (
                    Element (Fd, Literal (Int 2), Some (
                      Attribute (Count, Literal (Int 9)))))))
            )))
          )
        )),
        Raise (Literal (String "fd(0) count is not zero"))
      )
    ),
    Raise (Literal (String "fd(0) does not exist"))
  )

let test5 : Calc.stmt =
  Seq (
    Contains (Element (File, Literal (Path "/path/to/file")),
      Get ("v", OnElement (File, Literal (Path "/path/to/file"),
                  AttrAccess Count)),
      Seq (
        Add (Element (File, Literal (Path "/path/to/file"), None)),
        Get ("v", OnElement (File, Literal (Path "/path/to/file"),
                    AttrAccess Count))
      )
    ),
    Cond (Function (IsZero, Variable "v"),
      Add (Element (Fd, Literal (Int 1), None)),
      Add (Element (Fd, Literal (Int 2), None))
    )
  )

let interp (p : Calc.stmt) : CalcInterp.interp_res =
  CalcInterp.interpret p CalcInterp.init_interp_state Calc.VariableMap.empty
    (fun s _ -> Success s)
    (* Yield results in an error *)
    (fun _ _ _ -> Err "Nothing to yield to")
    (* Ret is okay only if we return a unit value *)
    (fun s _ (_, t) -> if Calc.isUnit t then Success s else Err "Nothing to return to")
    (* Raise converts the value into an Err *)
    (fun _ _ (v, _) -> Err (string_of_value v))

let test (p : Calc.stmt) : unit =
  match string_of_interp_res (interp p) with
  | Ok s | Error s -> Printf.printf "\n%s\n" s
