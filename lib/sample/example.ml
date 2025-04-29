open Calculus.Ast

type atts = Content
type elms = File
type lits = String of string | Path of string
type prim = String | Path | Env

type empty = |

module rec Calc : Ast_Defs
  with type variable  = string
  with type attribute = atts
  with type element   = elms
  with type literal   = lits
  with type primTy    = prim

  with type namedTy   = empty
  with type structTy  = empty
  with type funct     = empty
= struct
  type primTy = prim

  type field  = string
  module FieldMap = Map.Make(String)

  type namedTy  = empty
   and structTy = empty
   and typ = Product   of typ * typ
           | Primitive of primTy
           | Named     of namedTy
           | Struct    of structTy

  type funct = empty

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

  type env = (value * typ) VariableMap.t

  type attribute = atts
  type element   = elms

  type expr = Function of funct * expr
            | Literal  of literal
            | Variable of variable
            | Pair     of expr * expr
            | Env

  type qual = Attribute   of attribute * expr * qual list
            | Element     of element * expr * qual list
            | NotElement  of element * expr
  type attr = AttrAccess  of attribute
            | OnAttribute of attribute * attr
            | OnElement   of element * expr * attr
  type elem = Element     of element * expr
            | NotElement  of element * expr
            | OnAttribute of attribute * elem
            | OnElement   of element * expr * elem

  type action = |
   and stmt   = Action   of variable * action * expr * stmt
              | Assign   of variable * expr * stmt
              | Add      of qual * stmt
              | Get      of variable * attr * stmt
              | Contains of elem * stmt * stmt
              | Cond     of expr * stmt * stmt
              | Loop     of variable * expr * stmt * stmt
              | Match    of expr * variable * stmt * stmt
              | Fail     of string
              | Return   of expr

  let namedTyDef : namedTy -> typ * typ = function _ -> .
  let structTyDef : structTy -> _ = function _ -> .

  let funcDef : funct -> _ = function _ -> .

  let literalTyp : literal -> primTy = function
    | String _ -> String
    | Path   _ -> Path

  let attributeDef : attribute -> typ = function
    | Content -> Primitive String

  let elementDef : element -> typ = function
    | File -> Primitive Path

  let actionDef : action -> _ = function _ -> .

  let isTruthType (_ : typ)   : bool = false
  let asTruth     (_ : value) : bool option = None
  let boolAsValue (_ : bool)  : value = failwith "No boolean support"

  let isUnit      (_ : typ)   : bool = false

  let envType : typ = Primitive Env
  let envToVal (_ : env) : value = failwith "No environment support"
  let envFromVal (_ : value) : env = failwith "No environment support"

  type constr = IsBool of bool | IsConstructor of bool * (id * typ)
  type result_constraint = IsBool        of value * bool
                         | IsConstructor of value * (bool * (id * typ))
                         | IsEqual       of id * value
  type func_constraints = Unreducible | Reducible of result_constraint list list

  let reduceFuncConstraint : funct -> _ = function _ -> .
end

module CalcInterp = Calculus.Interp.Interp(Calc)

let rec string_of_value (v : Calc.value) : string =
  match v with
  | Unknown (Loop x, _)   -> "?loop(" ^ string_of_int x ^ ")"
  | Unknown (Val x, _)    -> "?" ^ string_of_int x
  | Literal (String s, _) -> "\"" ^ s ^ "\""
  | Literal (Path p, _)   -> "'" ^ p ^ "'"
  | Pair (x, y, _) -> "(" ^ string_of_value x ^ ", " ^ string_of_value y ^ ")"
  | Struct (_, _) -> .
  | Constructor (_, _, _) -> .
  | Function (_, _, _) -> .

let string_of_element (e : Calc.element) : string =
  match e with
  | File -> "file"

let string_of_attribute (a : Calc.attribute) : string =
  match a with
  | Content -> "content"

let string_of_list empty lhs sep rhs f lst : string =
  if List.is_empty lst
  then empty
  else lhs ^ String.concat sep (List.map f lst) ^ rhs

let string_of_state (state: CalcInterp.state) : string =
  let rec inner_string_of_state empty lhs rhs (state: CalcInterp.state) =
    let State(elems, attrs) = state
    in string_of_list empty lhs ", " rhs (fun s -> s)
      (List.map
        (fun ((elem, v, neg), s) ->
          (if neg then "not " else "")
          ^ string_of_element elem ^ "(" ^ string_of_value v ^ ")"
          ^ inner_string_of_state "" ": < " " >" s)
        (CalcInterp.ElementMap.to_list elems)
      @
      List.map
        (fun (attr, (v, s)) ->
          string_of_attribute attr ^ " = " ^ string_of_value v
          ^ inner_string_of_state "" ": < " " >" s)
        (CalcInterp.AttributeMap.to_list attrs))
  in inner_string_of_state "<>" "< " " >" state

let string_of_loop_info (i: CalcInterp.loop_info) : string =
  match i with
  | AllUnknown i -> "#" ^ string_of_int i
  | AllKnown v -> string_of_value v
  | LastKnown (i, v) -> "#" ^ string_of_int i ^ "/" ^ string_of_value v

let string_of_prg_type (state : CalcInterp.prg_type) : string =
  Printf.sprintf "%s --> %s [{ %s }, { %s }, { %s }]"
    (string_of_state state.init)
    (string_of_state state.final)
    (String.concat ", "
      (List.map (fun (v, i) -> string_of_value v ^ ": " ^ string_of_loop_info i)
        (CalcInterp.ValueMap.to_list state.loops)))
    (String.concat ", "
      (List.map (fun (v, b) -> string_of_value v ^ " = " ^ string_of_bool b)
        (CalcInterp.ValueMap.to_list state.bools)))
    (String.concat ", "
      (List.map (fun (v, (b, w)) -> string_of_value v ^ " = "
                  ^ (if b then "L" else "R") ^ "(" ^ string_of_value w ^ ")")
        (CalcInterp.ValueMap.to_list state.constrs)))

let string_of_results (res : CalcInterp.prg_res list) : (string, string) result =
  let rec process (res : CalcInterp.prg_res list) : string list * string list =
    match res with
    | [] -> ([], [])
    | Err msg :: tl ->
        let (succs, fails) = process tl
        in (succs, msg :: fails)
    | Ok (state, _) :: tl ->
        let (succs, fails) = process tl
        in (string_of_prg_type state :: succs, fails)
  in match process res with
  | ([], errors) -> Error(String.concat "\n" errors)
  | (states, _) -> Ok(String.concat "\n" states)

let example1 : Calc.stmt = 
  Get ("c", OnElement (File, Variable "S", AttrAccess Content),
  Add (Element (File, Variable "D", [Attribute (Content, Variable "c", [])]),
  Add (NotElement (File, Variable "S"),
  Return (Literal (String "returned")))))

let full1 : Calc.stmt =
  Assign ("S", Literal (Path "/path/to/src"),
  Assign ("D", Literal (Path "/path/to/dst"),
  Contains (Element (File, Variable "S"),
    example1,
    Fail "Missing source file")))

let example2 : Calc.stmt =
  Contains (Element (File, Variable "S"),
    example1,
    Return (Literal (String "returned")))

let full2 : Calc.stmt =
  Assign ("S", Literal (Path "/path/to/src"),
  Assign ("D", Literal (Path "/path/to/dst"),
  example2))

let res1 = string_of_results (CalcInterp.interpret full1 (Primitive String))
let res2 = string_of_results (CalcInterp.interpret full2 (Primitive String))
